# Copyright (c) 2015, Menno Smits
# Released subject to the New BSD License
# Please see http://en.wikipedia.org/wiki/BSD_licenses

import asyncio
import functools
import importlib
import itertools
import os
import re
import ssl as ssl_lib
import sys
import warnings
from datetime import date, datetime
from logging import getLogger, LoggerAdapter
from operator import itemgetter
from typing import List, Optional

from . import exceptions, response_lexer
from .datetime_util import datetime_to_INTERNALDATE, format_criteria_date
from .imap_utf7 import decode as decode_utf7
from .imap_utf7 import encode as encode_utf7
from .response_parser import (
    parse_fetch_response,
    parse_message_list,
    parse_response,
)
from .util import assert_imap_protocol, chunk, to_bytes, to_unicode

# Re-import shared helpers from imapclient.py to avoid duplication
from .imapclient import (
    _RE_SELECT_RESPONSE,
    MailboxQuotaRoots,
    Namespace,
    Quota,
    SocketTimeout,
    _dict_bytes_normaliser,
    _is8bit,
    _iter_with_last,
    _literal,
    _normalise_search_criteria,
    _normalise_sort_criteria,
    _parse_quota,
    _parse_untagged_response,
    _POPULAR_PERSONAL_NAMESPACES,
    _POPULAR_SPECIAL_FOLDERS,
    _quote,
    _quoted,
    as_pairs,
    as_triplets,
    debug_trunc,
    IMAPlibLoggerAdapter,
    join_message_ids,
    normalise_text_list,
    seq_to_parenstr,
    seq_to_parenstr_upper,
    utf7_decode_sequence,
)

# Lazy import for aioimaplib: only loaded when AsyncIMAPClient is actually
# instantiated, so that ``import imapclient`` never fails in environments
# where the deps/ tree is absent (e.g. wheel/sdist installs that only
# need the sync client).
_aioimaplib = None


def _import_aioimaplib():
    """Import aioimaplib on first use.

    The resolution order is:

    1. Try a normal ``import aioimaplib`` – this succeeds when the
       package is pip-installed (e.g.
       ``pip install aioimaplib@git+https://github.com/canarymail/aioimaplib``).
    2. Fall back to the vendored copy at ``deps/aioimaplib/src`` which
       is available in development / editable-install checkouts.
    3. If neither is available raise ``ModuleNotFoundError`` with an
       actionable message.
    """
    global _aioimaplib
    if _aioimaplib is not None:
        return _aioimaplib

    try:
        _aioimaplib = importlib.import_module("aioimaplib")
    except ModuleNotFoundError:
        # Vendored fallback for development checkouts
        _deps_path = os.path.join(
            os.path.dirname(__file__), "..", "deps", "aioimaplib", "src"
        )
        _deps_abs = os.path.abspath(_deps_path)
        if os.path.isdir(_deps_abs):
            if _deps_abs not in sys.path:
                sys.path.insert(0, _deps_abs)
            _aioimaplib = importlib.import_module("aioimaplib")
        else:
            raise ModuleNotFoundError(
                "aioimaplib is required for AsyncIMAPClient.  Install it with:\n"
                "  pip install aioimaplib@git+https://github.com/canarymail/aioimaplib\n"
                "or clone it into deps/aioimaplib in the source tree."
            ) from None

    # Register extension commands that the sync client patches into
    # imaplib.Commands but are missing from aioimaplib.Commands.
    _cmds = _aioimaplib.Commands
    if "XLIST" not in _cmds:
        _cmds["XLIST"] = ("NONAUTH", "AUTH", "SELECTED")
    if "ID" not in _cmds:
        _cmds["ID"] = ("NONAUTH", "AUTH", "SELECTED")

    return _aioimaplib

logger = getLogger(__name__)

__all__ = [
    "AsyncIMAPClient",
    "SocketTimeout",
    "DELETED",
    "SEEN",
    "ANSWERED",
    "FLAGGED",
    "DRAFT",
    "RECENT",
]

# System flags
DELETED = rb"\Deleted"
SEEN = rb"\Seen"
ANSWERED = rb"\Answered"
FLAGGED = rb"\Flagged"
DRAFT = rb"\Draft"
RECENT = rb"\Recent"  # This flag is read-only

# Special folders, see RFC6154
ALL = rb"\All"
ARCHIVE = rb"\Archive"
DRAFTS = rb"\Drafts"
JUNK = rb"\Junk"
SENT = rb"\Sent"
TRASH = rb"\Trash"


def _async_require_capability(capability):
    """Decorator raising CapabilityError when a capability is not available.

    Async-aware version for AsyncIMAPClient methods.  Ensures the client
    is connected before checking capabilities so that pre-connect calls
    (e.g. ``starttls()`` on a fresh client) do not spuriously fail.
    """

    def actual_decorator(func):
        @functools.wraps(func)
        async def wrapper(client, *args, **kwargs):
            # Ensure connected so server capabilities are populated.
            await client._imap.connect()
            client._apply_read_timeout()
            if not await client.has_capability(capability):
                raise exceptions.CapabilityError(
                    "Server does not support {} capability".format(capability)
                )
            return await func(client, *args, **kwargs)

        return wrapper

    return actual_decorator


def _translate_aioimaplib_error(imap, exc):
    """Translate an aioimaplib exception to the corresponding IMAPClient exception.

    aioimaplib defines its own ``IMAP4.error`` / ``IMAP4.abort`` /
    ``IMAP4.readonly`` hierarchy which is separate from ``imaplib``'s.
    We translate them so callers always see the familiar
    ``exceptions.IMAPClient*`` types.

    The checks are ordered most-specific-first (readonly → abort → error)
    because ``readonly`` is a subclass of ``abort`` which is a subclass of
    ``error``.
    """
    if isinstance(exc, imap.readonly):
        return exceptions.IMAPClientReadOnlyError(str(exc))
    if isinstance(exc, imap.abort):
        return exceptions.IMAPClientAbortError(str(exc))
    if isinstance(exc, imap.error):
        return exceptions.IMAPClientError(str(exc))
    return exc


class AsyncIMAPClient:
    """An async connection to the IMAP server specified by *host*.

    This is the async equivalent of :py:class:`imapclient.IMAPClient`.
    All I/O methods are coroutines that must be awaited.

    *port* defaults to 993, or 143 if *ssl* is ``False``.

    If *use_uid* is ``True`` unique message UIDs be used for all calls
    that accept message ids (defaults to ``True``).

    If *ssl* is ``True`` (the default) a secure connection will be made.
    Otherwise an insecure connection over plain text will be established.

    If *ssl* is ``True`` the optional *ssl_context* argument can be
    used to provide an ``ssl.SSLContext`` instance used to control
    SSL/TLS connection parameters.

    If *stream* is ``True`` then *host* is used as the command to run
    to establish a connection to the IMAP server.

    Use *timeout* to specify a timeout for the socket connected to the
    IMAP server. The timeout can be either a float number, or an instance
    of :py:class:`imapclient.SocketTimeout`.

    The *normalise_times* attribute specifies whether datetimes
    returned by ``fetch()`` are normalised to the local system time.

    Can be used as an async context manager:

    >>> async with AsyncIMAPClient(host="imap.foo.org") as client:
    ...     await client.login("bar@foo.org", "passwd")
    """

    Error = exceptions.IMAPClientError
    AbortError = exceptions.IMAPClientAbortError
    ReadOnlyError = exceptions.IMAPClientReadOnlyError

    def __init__(
        self,
        host: str,
        port: int = None,
        use_uid: bool = True,
        ssl: bool = True,
        stream: bool = False,
        ssl_context: Optional[ssl_lib.SSLContext] = None,
        timeout: Optional[float] = None,
        sock=None,
    ):
        if stream:
            if port is not None:
                raise ValueError("can't set 'port' when 'stream' True")
            if ssl:
                raise ValueError("can't use 'ssl' when 'stream' is True")
        elif port is None:
            port = ssl and 993 or 143

        if ssl and port == 143:
            logger.warning(
                "Attempting to establish an encrypted connection "
                "to a port (143) often used for unencrypted "
                "connections"
            )

        self.host = host
        self.port = port
        self.ssl = ssl
        self.ssl_context = ssl_context
        self.stream = stream
        self.use_uid = use_uid
        self.folder_encode = True
        self.normalise_times = True

        if not isinstance(timeout, SocketTimeout):
            timeout = SocketTimeout(timeout, timeout)

        self._timeout = timeout
        self._starttls_done = False
        self._cached_capabilities = None
        self._idle_tag = None
        self._sock = sock

        self._imap = self._create_IMAP4()

    async def __aenter__(self):
        await self._imap.connect()
        self._apply_read_timeout()
        logger.debug(
            "Connected to host %s over %s",
            self.host,
            "SSL/TLS" if self.ssl else "plain text",
        )
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Logout and close the connection when exiting the context manager."""
        try:
            await self.logout()
        except Exception:
            try:
                await self.shutdown()
            except Exception as e:
                logger.info("Could not close the connection cleanly: %s", e)

    def _create_IMAP4(self):
        aiolib = _import_aioimaplib()
        connect_timeout = getattr(self._timeout, "connect", None)
        read_timeout = getattr(self._timeout, "read", None)

        if self.stream:
            imap = aiolib.IMAP4_stream(self.host)
        elif self.ssl:
            ssl_context = self.ssl_context
            if ssl_context is None:
                ssl_context = ssl_lib.create_default_context(
                    purpose=ssl_lib.Purpose.SERVER_AUTH
                )
            imap = aiolib.IMAP4_SSL(
                self.host,
                self.port,
                ssl_context=ssl_context,
                timeout=connect_timeout,
                sock=self._sock,
            )
        else:
            imap = aiolib.IMAP4(self.host, self.port, timeout=connect_timeout, sock=self._sock)

        return imap

    def _apply_read_timeout(self):
        """Apply ``SocketTimeout.read`` to the aioimaplib transport.

        aioimaplib uses a single ``timeout`` attribute for both connection and
        command I/O.  ``open()`` sets it from the *connect* timeout, so we
        must overwrite it after connection is established so that all
        subsequent command round-trips honour ``SocketTimeout.read``.
        """
        read_timeout = getattr(self._timeout, "read", None)
        if read_timeout is not None:
            self._imap.timeout = read_timeout

    @property
    def _sock(self):
        warnings.warn("_sock is deprecated. Use socket().", DeprecationWarning)
        return self.socket()

    def socket(self):
        """Returns socket used to connect to server.

        The socket is provided for polling purposes only.
        """
        return self._imap.socket()

    @_async_require_capability("STARTTLS")
    async def starttls(self, ssl_context=None):
        """Switch to an SSL encrypted connection by sending a STARTTLS command.

        The *ssl_context* argument is optional and should be a
        :py:class:`ssl.SSLContext` object.

        Raises :py:exc:`Error` if the SSL connection could not be established.

        Raises :py:exc:`AbortError` if the server does not support STARTTLS
        or an SSL connection is already established.
        """
        if self.ssl or self._starttls_done:
            raise exceptions.IMAPClientAbortError("TLS session already established")

        if ssl_context is None:
            ssl_context = ssl_lib.create_default_context(
                purpose=ssl_lib.Purpose.SERVER_AUTH
            )

        try:
            typ, data = await self._imap._simple_command("STARTTLS")
            if typ != "OK":
                raise exceptions.IMAPClientError(
                    "Couldn't establish TLS session: %s" % data[0]
                )
            # Perform TLS upgrade on the underlying transport.
            if self._imap._writer is None:
                raise exceptions.IMAPClientAbortError(
                    "TLS upgrade requires socket transport"
                )
            await self._imap._writer.start_tls(
                ssl_context, server_hostname=self._imap.host
            )
            self._imap._tls_established = True
            await self._imap._get_capabilities()
        except self._imap.abort as e:
            raise exceptions.IMAPClientAbortError(str(e))
        except self._imap.error as e:
            raise exceptions.IMAPClientError(str(e))

        self._starttls_done = True
        self._cached_capabilities = None
        return data[0]

    async def login(self, username: str, password: str):
        """Login using *username* and *password*, returning the
        server response.
        """
        try:
            rv = await self._command_and_check(
                "login",
                to_unicode(username),
                to_unicode(password),
                unpack=True,
            )
        except exceptions.IMAPClientError as e:
            raise exceptions.LoginError(str(e))

        logger.debug("Logged in as %s", username)
        return rv

    async def oauth2_login(
        self,
        user: str,
        access_token: str,
        mech: str = "XOAUTH2",
        vendor: Optional[str] = None,
    ):
        """Authenticate using the OAUTH2 or XOAUTH2 methods."""
        auth_string = "user=%s\1auth=Bearer %s\1" % (user, access_token)
        if vendor:
            auth_string += "vendor=%s\1" % vendor
        auth_string += "\1"
        try:
            return await self._command_and_check(
                "authenticate", mech, lambda x: auth_string
            )
        except exceptions.IMAPClientError as e:
            raise exceptions.LoginError(str(e))

    async def oauthbearer_login(self, identity, access_token):
        """Authenticate using the OAUTHBEARER method."""
        if identity:
            gs2_header = "n,a=%s," % identity.replace("=", "=3D").replace(",", "=2C")
        else:
            gs2_header = "n,,"
        http_authz = "Bearer %s" % access_token
        auth_string = "%s\1auth=%s\1\1" % (gs2_header, http_authz)
        try:
            return await self._command_and_check(
                "authenticate", "OAUTHBEARER", lambda x: auth_string
            )
        except exceptions.IMAPClientError as e:
            raise exceptions.LoginError(str(e))

    async def plain_login(self, identity, password, authorization_identity=None):
        """Authenticate using the PLAIN method (requires server support)."""
        if not authorization_identity:
            authorization_identity = ""
        auth_string = "%s\0%s\0%s" % (authorization_identity, identity, password)
        try:
            return await self._command_and_check(
                "authenticate", "PLAIN", lambda _: auth_string, unpack=True
            )
        except exceptions.IMAPClientError as e:
            raise exceptions.LoginError(str(e))

    async def sasl_login(self, mech_name, mech_callable):
        """Authenticate using a provided SASL mechanism (requires server support)."""
        try:
            return await self._command_and_check(
                "authenticate", mech_name, mech_callable, unpack=True
            )
        except exceptions.IMAPClientError as e:
            raise exceptions.LoginError(str(e))

    async def logout(self):
        """Logout, returning the server response."""
        try:
            typ, data = await self._imap.logout()
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e
        self._check_resp("BYE", "logout", typ, data)
        logger.debug("Logged out, connection closed")
        return data[0]

    async def shutdown(self) -> None:
        """Close the connection to the IMAP server (without logging out)."""
        await self._imap.shutdown()
        logger.info("Connection closed")

    @_async_require_capability("ENABLE")
    async def enable(self, *capabilities):
        """Activate one or more server side capability extensions.

        A list of the requested extensions that were successfully
        enabled on the server is returned.
        """
        if self._imap.state != "AUTH":
            raise exceptions.IllegalStateError(
                "ENABLE command illegal in state %s" % self._imap.state
            )

        resp = await self._raw_command_untagged(
            b"ENABLE",
            [to_bytes(c) for c in capabilities],
            uid=False,
            response_name="ENABLED",
            unpack=True,
        )
        if not resp:
            return []
        return resp.split()

    @_async_require_capability("ID")
    async def id_(self, parameters=None):
        """Issue the ID command, returning a dict of server implementation
        fields.
        """
        if parameters is None:
            args = "NIL"
        else:
            if not isinstance(parameters, dict):
                raise TypeError("'parameters' should be a dictionary")
            args = seq_to_parenstr(
                _quote(v) for v in itertools.chain.from_iterable(parameters.items())
            )

        try:
            typ, data = await self._imap._simple_command("ID", args)
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e
        self._checkok("id", typ, data)
        typ, data = self._imap._untagged_response(typ, data, "ID")
        return parse_response(data)

    async def capabilities(self):
        """Returns the server capability list.

        If the session is authenticated and the server has returned an
        untagged CAPABILITY response at authentication time, this
        response will be returned. Otherwise, the CAPABILITY command
        will be issued to the server, with the results cached for
        future calls.
        """
        if self._starttls_done and self._imap.state == "NONAUTH":
            self._cached_capabilities = None
            return await self._do_capabilites()

        if self._cached_capabilities:
            return self._cached_capabilities

        untagged = _dict_bytes_normaliser(self._imap.untagged_responses)
        response = untagged.pop("CAPABILITY", None)
        if response:
            self._cached_capabilities = self._normalise_capabilites(response[0])
            return self._cached_capabilities

        if self._imap.state in ("SELECTED", "AUTH"):
            self._cached_capabilities = await self._do_capabilites()
            return self._cached_capabilities

        # Return capabilities that aioimaplib requested at connection time
        return tuple(to_bytes(c) for c in self._imap.capabilities)

    async def _do_capabilites(self):
        raw_response = await self._command_and_check("capability", unpack=True)
        return self._normalise_capabilites(raw_response)

    def _normalise_capabilites(self, raw_response):
        raw_response = to_bytes(raw_response)
        return tuple(raw_response.upper().split())

    async def has_capability(self, capability):
        """Return ``True`` if the IMAP server has the given *capability*."""
        return to_bytes(capability).upper() in await self.capabilities()

    @_async_require_capability("NAMESPACE")
    async def namespace(self):
        """Return the namespace for the account as a (personal, other,
        shared) tuple.
        """
        data = await self._command_and_check("namespace")
        parts = []
        for item in parse_response(data):
            if item is None:
                parts.append(item)
            else:
                converted = []
                for prefix, separator in item:
                    if self.folder_encode:
                        prefix = decode_utf7(prefix)
                    converted.append((prefix, to_unicode(separator)))
                parts.append(tuple(converted))
        return Namespace(*parts)

    async def list_folders(self, directory="", pattern="*"):
        """Get a listing of folders on the server as a list of
        ``(flags, delimiter, name)`` tuples.
        """
        return await self._do_list("LIST", directory, pattern)

    @_async_require_capability("XLIST")
    async def xlist_folders(self, directory="", pattern="*"):
        """Execute the XLIST command, returning ``(flags, delimiter,
        name)`` tuples.
        """
        return await self._do_list("XLIST", directory, pattern)

    async def list_sub_folders(self, directory="", pattern="*"):
        """Return a list of subscribed folders on the server as
        ``(flags, delimiter, name)`` tuples.
        """
        return await self._do_list("LSUB", directory, pattern)

    async def _do_list(self, cmd, directory, pattern):
        directory = self._normalise_folder(directory)
        pattern = self._normalise_folder(pattern)
        try:
            typ, dat = await self._imap._simple_command(cmd, directory, pattern)
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e
        self._checkok(cmd, typ, dat)
        typ, dat = self._imap._untagged_response(typ, dat, cmd)
        return self._proc_folder_list(dat)

    def _proc_folder_list(self, folder_data):
        folder_data = [item for item in folder_data if item not in (b"", None)]

        ret = []
        parsed = parse_response(folder_data)
        for flags, delim, name in chunk(parsed, size=3):
            if isinstance(name, int):
                name = str(name)
            elif self.folder_encode:
                name = decode_utf7(name)

            ret.append((flags, delim, name))
        return ret

    async def find_special_folder(self, folder_flag):
        """Try to locate a special folder, like the Sent or Trash folder.

        Returns the name of the folder if found, or None otherwise.
        """
        for folder in await self.list_folders():
            if folder and len(folder[0]) > 0 and folder_flag in folder[0]:
                return folder[2]

        if await self.has_capability("NAMESPACE"):
            personal_namespaces = (await self.namespace()).personal
        else:
            personal_namespaces = _POPULAR_PERSONAL_NAMESPACES

        for personal_namespace in personal_namespaces:
            for pattern in _POPULAR_SPECIAL_FOLDERS.get(folder_flag, tuple()):
                pattern = personal_namespace[0] + pattern
                sent_folders = await self.list_folders(pattern=pattern)
                if sent_folders:
                    return sent_folders[0][2]

        return None

    async def select_folder(self, folder, readonly=False):
        """Set the current folder on the server.

        Returns a dictionary containing the ``SELECT`` response.
        """
        await self._command_and_check(
            "select", self._normalise_folder(folder), readonly
        )
        return self._process_select_response(self._imap.untagged_responses)

    @_async_require_capability("UNSELECT")
    async def unselect_folder(self):
        r"""Unselect the current folder and release associated resources.

        Unlike ``close_folder``, the ``UNSELECT`` command does not expunge
        the mailbox.

        Returns the UNSELECT response string returned by the server.
        """
        logger.debug("< UNSELECT")
        try:
            _typ, data = await self._imap._simple_command("UNSELECT")
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e
        return data[0]

    def _process_select_response(self, resp):
        untagged = _dict_bytes_normaliser(resp)
        out = {}

        for line in untagged.get("OK", []):
            match = _RE_SELECT_RESPONSE.match(line)
            if match:
                key = match.group("key")
                if key == b"PERMANENTFLAGS":
                    out[key] = tuple(match.group("data").split())

        for key, value in untagged.items():
            key = key.upper()
            if key in (b"OK", b"PERMANENTFLAGS"):
                continue
            if key in (
                b"EXISTS",
                b"RECENT",
                b"UIDNEXT",
                b"UIDVALIDITY",
                b"HIGHESTMODSEQ",
            ):
                value = int(value[0])
            elif key == b"READ-WRITE":
                value = True
            elif key == b"FLAGS":
                value = tuple(value[0][1:-1].split())
            out[key] = value
        return out

    async def noop(self):
        """Execute the NOOP command.

        The return value is the server command response message
        followed by a list of status responses.
        """
        await self._imap.connect()
        self._apply_read_timeout()
        try:
            tag = await self._imap._command("NOOP")
            return await self._consume_until_tagged_response(tag, "NOOP")
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e

    @_async_require_capability("IDLE")
    async def idle(self):
        """Put the server into IDLE mode.

        In this mode the server will return unsolicited responses
        about changes to the selected mailbox. This method returns
        immediately. Use ``idle_check()`` to look for IDLE responses
        and ``idle_done()`` to stop IDLE mode.

        .. note::

            Any other commands issued while the server is in IDLE
            mode will fail.

        See :rfc:`2177` for more information about the IDLE extension.
        """
        try:
            self._idle_tag = await self._imap._command("IDLE")
            resp = await self._imap._get_response()
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e
        if resp is not None:
            raise exceptions.IMAPClientError("Unexpected IDLE response: %s" % resp)

    @_async_require_capability("IDLE")
    async def idle_check(self, timeout=None):
        """Check for any IDLE responses sent by the server.

        This method should only be called if the server is in IDLE
        mode (see ``idle()``).

        By default, this method will block until an IDLE response is
        received. If *timeout* is provided, the call will block for at
        most this many seconds while waiting for an IDLE response.

        The return value is a list of received IDLE responses.
        """
        resps = []
        try:
            line = await asyncio.wait_for(
                self._imap._get_line(), timeout=timeout
            )
            resps.append(_parse_untagged_response(line))
            # Try to read more lines without blocking long
            while True:
                try:
                    line = await asyncio.wait_for(
                        self._imap._get_line(), timeout=0.1
                    )
                    resps.append(_parse_untagged_response(line))
                except asyncio.TimeoutError:
                    break
        except asyncio.TimeoutError:
            pass
        return resps

    @_async_require_capability("IDLE")
    async def idle_done(self):
        """Take the server out of IDLE mode.

        This method should only be called if the server is already in
        IDLE mode.

        The return value is of the form ``(command_text,
        idle_responses)`` where *command_text* is the text sent by the
        server when the IDLE command finished and *idle_responses* is a
        list of parsed idle responses received since the last call to
        ``idle_check()`` (if any).
        """
        logger.debug("< DONE")
        await self._imap.send(b"DONE\r\n")
        return await self._consume_until_tagged_response(self._idle_tag, "IDLE")

    async def folder_status(self, folder, what=None):
        """Return the status of *folder*.

        *what* should be a sequence of status items to query. This
        defaults to ``('MESSAGES', 'RECENT', 'UIDNEXT', 'UIDVALIDITY',
        'UNSEEN')``.

        Returns a dictionary of the status items for the folder with
        keys matching *what*.
        """
        if what is None:
            what = ("MESSAGES", "RECENT", "UIDNEXT", "UIDVALIDITY", "UNSEEN")
        else:
            what = normalise_text_list(what)
        what_ = "(%s)" % (" ".join(what))

        fname = self._normalise_folder(folder)
        data = await self._command_and_check("status", fname, what_)
        response = parse_response(data)
        status_items = response[-1]
        return dict(as_pairs(status_items))

    async def close_folder(self):
        """Close the currently selected folder, returning the server
        response string.
        """
        return await self._command_and_check("close", unpack=True)

    async def create_folder(self, folder):
        """Create *folder* on the server returning the server response string."""
        return await self._command_and_check(
            "create", self._normalise_folder(folder), unpack=True
        )

    async def rename_folder(self, old_name, new_name):
        """Change the name of a folder on the server."""
        return await self._command_and_check(
            "rename",
            self._normalise_folder(old_name),
            self._normalise_folder(new_name),
            unpack=True,
        )

    async def delete_folder(self, folder):
        """Delete *folder* on the server returning the server response string."""
        return await self._command_and_check(
            "delete", self._normalise_folder(folder), unpack=True
        )

    async def folder_exists(self, folder):
        """Return ``True`` if *folder* exists on the server."""
        return len(await self.list_folders("", folder)) > 0

    async def subscribe_folder(self, folder):
        """Subscribe to *folder*, returning the server response string."""
        return await self._command_and_check(
            "subscribe", self._normalise_folder(folder)
        )

    async def unsubscribe_folder(self, folder):
        """Unsubscribe to *folder*, returning the server response string."""
        return await self._command_and_check(
            "unsubscribe", self._normalise_folder(folder)
        )

    async def search(self, criteria="ALL", charset=None):
        """Return a list of messages ids from the currently selected
        folder matching *criteria*.

        *criteria* should be a sequence of one or more criteria items.
        Each criteria item may be either unicode or bytes.

        IMAPClient will perform conversion and quoting as required.

        The returned list of message ids will have a special *modseq*
        attribute. This is set if the server included a MODSEQ value
        to the search response.
        """
        return await self._search(criteria, charset)

    @_async_require_capability("X-GM-EXT-1")
    async def gmail_search(self, query, charset="UTF-8"):
        """Search using Gmail's X-GM-RAW attribute.

        *query* should be a valid Gmail search query string.
        """
        return await self._search([b"X-GM-RAW", query], charset)

    async def _search(self, criteria, charset):
        args = []
        if charset:
            args.extend([b"CHARSET", to_bytes(charset)])
        args.extend(_normalise_search_criteria(criteria, charset))

        try:
            data = await self._raw_command_untagged(b"SEARCH", args)
        except exceptions.IMAPClientError as e:
            m = re.match(r"SEARCH command error: BAD \[(.+)\]", str(e))
            if m:
                raise exceptions.InvalidCriteriaError(
                    "{original_msg}\n\n"
                    "This error may have been caused by a syntax error in the criteria: "
                    "{criteria}\nPlease refer to the documentation for more information "
                    "about search criteria syntax..\n"
                    "https://imapclient.readthedocs.io/en/master/#imapclient.IMAPClient.search".format(
                        original_msg=m.group(1),
                        criteria=(
                            '"%s"' % criteria
                            if not isinstance(criteria, list)
                            else criteria
                        ),
                    )
                )
            raise

        return parse_message_list(data)

    @_async_require_capability("SORT")
    async def sort(self, sort_criteria, criteria="ALL", charset="UTF-8"):
        """Return a list of message ids from the currently selected
        folder, sorted by *sort_criteria* and optionally filtered by
        *criteria*.
        """
        args = [
            _normalise_sort_criteria(sort_criteria),
            to_bytes(charset),
        ]
        args.extend(_normalise_search_criteria(criteria, charset))
        ids = await self._raw_command_untagged(b"SORT", args, unpack=True)
        return [int(i) for i in ids.split()]

    async def thread(self, algorithm="REFERENCES", criteria="ALL", charset="UTF-8"):
        """Return a list of messages threads from the currently
        selected folder which match *criteria*.
        """
        algorithm = to_bytes(algorithm)
        if not await self.has_capability(b"THREAD=" + algorithm):
            raise exceptions.CapabilityError(
                "The server does not support %s threading algorithm" % algorithm
            )

        args = [algorithm, to_bytes(charset)] + _normalise_search_criteria(
            criteria, charset
        )
        data = await self._raw_command_untagged(b"THREAD", args)
        return parse_response(data)

    async def get_flags(self, messages):
        """Return the flags set for each message in *messages* from
        the currently selected folder.
        """
        response = await self.fetch(messages, ["FLAGS"])
        return self._filter_fetch_dict(response, b"FLAGS")

    async def add_flags(self, messages, flags, silent=False):
        """Add *flags* to *messages* in the currently selected folder."""
        return await self._store(
            b"+FLAGS", messages, flags, b"FLAGS", silent=silent
        )

    async def remove_flags(self, messages, flags, silent=False):
        """Remove one or more *flags* from *messages* in the currently
        selected folder.
        """
        return await self._store(
            b"-FLAGS", messages, flags, b"FLAGS", silent=silent
        )

    async def set_flags(self, messages, flags, silent=False):
        """Set the *flags* for *messages* in the currently selected
        folder.
        """
        return await self._store(
            b"FLAGS", messages, flags, b"FLAGS", silent=silent
        )

    async def get_gmail_labels(self, messages):
        """Return the label set for each message in *messages*."""
        response = await self.fetch(messages, [b"X-GM-LABELS"])
        response = self._filter_fetch_dict(response, b"X-GM-LABELS")
        return {msg: utf7_decode_sequence(labels) for msg, labels in response.items()}

    async def add_gmail_labels(self, messages, labels, silent=False):
        """Add *labels* to *messages* in the currently selected folder."""
        return await self._gm_label_store(
            b"+X-GM-LABELS", messages, labels, silent=silent
        )

    async def remove_gmail_labels(self, messages, labels, silent=False):
        """Remove one or more *labels* from *messages*."""
        return await self._gm_label_store(
            b"-X-GM-LABELS", messages, labels, silent=silent
        )

    async def set_gmail_labels(self, messages, labels, silent=False):
        """Set the *labels* for *messages* in the currently selected
        folder.
        """
        return await self._gm_label_store(
            b"X-GM-LABELS", messages, labels, silent=silent
        )

    async def delete_messages(self, messages, silent=False):
        """Delete one or more *messages* from the currently selected
        folder.
        """
        return await self.add_flags(messages, DELETED, silent=silent)

    async def fetch(self, messages, data, modifiers=None):
        """Retrieve selected *data* associated with one or more
        *messages* in the currently selected folder.

        *data* should be specified as a sequence of strings, one item
        per data selector.

        *modifiers* are required for some extensions to the IMAP
        protocol (eg. :rfc:`4551`).

        A dictionary is returned, indexed by message number. Each item
        in this dictionary is also a dictionary, with an entry
        corresponding to each item in *data*.
        """
        if not messages:
            return {}

        args = [
            "FETCH",
            join_message_ids(messages),
            seq_to_parenstr_upper(data),
            seq_to_parenstr_upper(modifiers) if modifiers else None,
        ]
        if self.use_uid:
            args.insert(0, "UID")

        await self._imap.connect()
        self._apply_read_timeout()
        try:
            tag = await self._imap._command(*args)
            typ, data = await self._imap._command_complete("FETCH", tag)
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e
        self._checkok("fetch", typ, data)
        typ, data = self._imap._untagged_response(typ, data, "FETCH")
        return parse_fetch_response(data, self.normalise_times, self.use_uid)

    async def append(self, folder, msg, flags=(), msg_time=None):
        """Append a message to *folder*.

        *msg* should be a string contains the full message including
        headers.

        *flags* should be a sequence of message flags to set.

        *msg_time* is an optional datetime instance specifying the
        date and time to set on the message.

        Returns the APPEND response as returned by the server.
        """
        if msg_time:
            time_val = '"%s"' % datetime_to_INTERNALDATE(msg_time)
            time_val = to_unicode(time_val)
        else:
            time_val = None
        return await self._command_and_check(
            "append",
            self._normalise_folder(folder),
            seq_to_parenstr(flags),
            time_val,
            to_bytes(msg),
            unpack=True,
        )

    @_async_require_capability("MULTIAPPEND")
    async def multiappend(self, folder, msgs):
        """Append messages to *folder* using the MULTIAPPEND feature from :rfc:`3502`.

        *msgs* must be an iterable. Each item must be either a string containing the
        full message including headers, or a dict.

        Returns the APPEND response from the server.
        """

        def chunks():
            for m in msgs:
                if isinstance(m, dict):
                    if "flags" in m:
                        yield to_bytes(seq_to_parenstr(m["flags"]))
                    if "date" in m:
                        yield to_bytes(
                            '"%s"' % datetime_to_INTERNALDATE(m["date"])
                        )
                    yield _literal(to_bytes(m["msg"]))
                else:
                    yield _literal(to_bytes(m))

        msgs = list(chunks())

        return await self._raw_command(
            b"APPEND",
            [self._normalise_folder(folder)] + msgs,
            uid=False,
        )

    async def copy(self, messages, folder):
        """Copy one or more messages from the current folder to
        *folder*. Returns the COPY response string returned by the
        server.
        """
        return await self._command_and_check(
            "copy",
            join_message_ids(messages),
            self._normalise_folder(folder),
            uid=True,
            unpack=True,
        )

    @_async_require_capability("MOVE")
    async def move(self, messages, folder):
        """Atomically move messages to another folder.

        Requires the MOVE capability, see :rfc:`6851`.
        """
        return await self._command_and_check(
            "move",
            join_message_ids(messages),
            self._normalise_folder(folder),
            uid=True,
            unpack=True,
        )

    async def expunge(self, messages=None):
        """Remove all messages from the currently selected folder that have the
        ``\\Deleted`` flag set.

        When *messages* are specified, remove the specified messages
        from the selected folder, provided those messages also have
        the ``\\Deleted`` flag set.
        """
        if messages:
            if not self.use_uid:
                raise ValueError("cannot EXPUNGE by ID when not using uids")
            return await self._command_and_check(
                "EXPUNGE", join_message_ids(messages), uid=True
            )
        await self._imap.connect()
        self._apply_read_timeout()
        try:
            tag = await self._imap._command("EXPUNGE")
            return await self._consume_until_tagged_response(tag, "EXPUNGE")
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e

    @_async_require_capability("UIDPLUS")
    async def uid_expunge(self, messages):
        """Expunge deleted messages with the specified message ids from the
        folder.
        """
        return await self._command_and_check(
            "EXPUNGE", join_message_ids(messages), uid=True
        )

    @_async_require_capability("ACL")
    async def getacl(self, folder):
        """Returns a list of ``(who, acl)`` tuples describing the
        access controls for *folder*.
        """
        data = await self._command_and_check(
            "getacl", self._normalise_folder(folder)
        )
        parts = list(response_lexer.TokenSource(data))
        parts = parts[1:]  # First item is folder name
        return [(parts[i], parts[i + 1]) for i in range(0, len(parts), 2)]

    @_async_require_capability("ACL")
    async def setacl(self, folder, who, what):
        """Set an ACL (*what*) for user (*who*) for a folder.

        Set *what* to an empty string to remove an ACL.
        """
        return await self._command_and_check(
            "setacl", self._normalise_folder(folder), who, what, unpack=True
        )

    @_async_require_capability("QUOTA")
    async def get_quota(self, mailbox="INBOX"):
        """Get the quotas associated with a mailbox.

        Returns a list of Quota objects.
        """
        return (await self.get_quota_root(mailbox))[1]

    @_async_require_capability("QUOTA")
    async def _get_quota(self, quota_root=""):
        """Get the quotas associated with a quota root.

        Returns a list of Quota objects.
        """
        return _parse_quota(
            await self._command_and_check("getquota", _quote(quota_root))
        )

    @_async_require_capability("QUOTA")
    async def get_quota_root(self, mailbox):
        """Get the quota roots for a mailbox.

        Return a tuple of MailboxQuotaRoots and list of Quota associated.
        """
        quota_root_rep = await self._raw_command_untagged(
            b"GETQUOTAROOT",
            to_bytes(mailbox),
            uid=False,
            response_name="QUOTAROOT",
        )
        quota_rep = self._imap.untagged_responses.pop("QUOTA", [])
        quota_root_rep = parse_response(quota_root_rep)
        quota_root = MailboxQuotaRoots(
            to_unicode(quota_root_rep[0]),
            [to_unicode(q) for q in quota_root_rep[1:]],
        )
        return quota_root, _parse_quota(quota_rep)

    @_async_require_capability("QUOTA")
    async def set_quota(self, quotas):
        """Set one or more quotas on resources.

        :param quotas: list of Quota objects
        """
        if not quotas:
            return

        quota_root = None
        set_quota_args = []

        for quota in quotas:
            if quota_root is None:
                quota_root = quota.quota_root
            elif quota_root != quota.quota_root:
                raise ValueError("set_quota only accepts a single quota root")

            set_quota_args.append("{} {}".format(quota.resource, quota.limit))

        set_quota_args = " ".join(set_quota_args)
        args = [to_bytes(_quote(quota_root)), to_bytes("({})".format(set_quota_args))]

        response = await self._raw_command_untagged(
            b"SETQUOTA", args, uid=False, response_name="QUOTA"
        )
        return _parse_quota(response)

    def _check_resp(self, expected, command, typ, data):
        """Check command responses for errors."""
        if typ != expected:
            raise exceptions.IMAPClientError(
                "%s failed: %s" % (command, to_unicode(data[0]))
            )

    async def _consume_until_tagged_response(self, tag, command):
        tagged_commands = self._imap.tagged_commands
        resps = []
        while True:
            line = await self._imap._get_response()
            if tagged_commands[tag]:
                break
            resps.append(_parse_untagged_response(line))
        typ, data = tagged_commands.pop(tag)
        self._checkok(command, typ, data)
        return data[0], resps

    async def _raw_command_untagged(
        self, command, args, response_name=None, unpack=False, uid=True
    ):
        try:
            typ, data = await self._raw_command(command, args, uid=uid)
        except exceptions.IMAPClientError:
            raise  # Already translated by _raw_command
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e
        if response_name is None:
            response_name = command
        typ, data = self._imap._untagged_response(
            typ, data, to_unicode(response_name)
        )
        self._checkok(to_unicode(command), typ, data)
        if unpack:
            return data[0]
        return data

    async def _raw_command(self, command, args, uid=True):
        """Run the specific command with the arguments given. 8-bit arguments
        are sent as literals. The return value is (typ, data).

        *command* should be specified as bytes.
        *args* should be specified as a list of bytes.
        """
        # Ensure we are connected before calling _new_tag() which needs
        # ``tagpre`` (only set during _connect()).
        await self._imap.connect()
        self._apply_read_timeout()

        command = command.upper()

        has_literal_plus = await self.has_capability("LITERAL+")

        if isinstance(args, tuple):
            args = list(args)
        if not isinstance(args, list):
            args = [args]

        tag = self._imap._new_tag()
        prefix = [to_bytes(tag)]
        if uid and self.use_uid:
            prefix.append(b"UID")
        prefix.append(command)

        line = []
        try:
            for item, is_last in _iter_with_last(prefix + args):
                if not isinstance(item, bytes):
                    raise ValueError("command args must be passed as bytes")

                if _is8bit(item):
                    if line:
                        out = b" ".join(line)
                        logger.debug("> %s", out)
                        await self._imap.send(out)
                        line = []

                    if isinstance(item, _quoted):
                        item = item.original
                    await self._send_literal(tag, item, has_literal_plus)
                    if not is_last:
                        await self._imap.send(b" ")
                else:
                    line.append(item)

            if line:
                out = b" ".join(line)
                logger.debug("> %s", out)
                await self._imap.send(out)

            await self._imap.send(b"\r\n")

            return await self._imap._command_complete(to_unicode(command), tag)
        except self._imap.error as e:
            raise _translate_aioimaplib_error(self._imap, e) from e

    async def _send_literal(self, tag, item, has_literal_plus):
        """Send a single literal for the command with *tag*."""
        if has_literal_plus:
            out = b" {" + str(len(item)).encode("ascii") + b"+}\r\n" + item
            logger.debug("> %s", debug_trunc(out, 64))
            await self._imap.send(out)
            return

        out = b" {" + str(len(item)).encode("ascii") + b"}\r\n"
        logger.debug("> %s", out)
        await self._imap.send(out)

        # Wait for continuation response
        while await self._imap._get_response():
            tagged_resp = self._imap.tagged_commands.get(tag)
            if tagged_resp:
                raise exceptions.IMAPClientAbortError(
                    "unexpected response while waiting for continuation response: "
                    + repr(tagged_resp)
                )

        logger.debug("   (literal) > %s", debug_trunc(item, 256))
        await self._imap.send(item)

    async def _command_and_check(
        self, command, *args, unpack: bool = False, uid: bool = False
    ):
        try:
            if uid and self.use_uid:
                command = to_unicode(command)
                typ, data = await self._imap.uid(command, *args)
            else:
                meth = getattr(self._imap, to_unicode(command))
                typ, data = await meth(*args)
        except self._imap.error as e:
            translated = _translate_aioimaplib_error(self._imap, e)
            raise type(translated)(
                "%s command error: %s" % (command, str(e))
            ) from e
        self._checkok(command, typ, data)
        if unpack:
            return data[0]
        return data

    def _checkok(self, command, typ, data):
        self._check_resp("OK", command, typ, data)

    async def _gm_label_store(self, cmd, messages, labels, silent):
        response = await self._store(
            cmd,
            messages,
            self._normalise_labels(labels),
            b"X-GM-LABELS",
            silent=silent,
        )
        return (
            {msg: utf7_decode_sequence(labels) for msg, labels in response.items()}
            if response
            else None
        )

    async def _store(self, cmd, messages, flags, fetch_key, silent):
        """Worker function for the various flag manipulation methods."""
        if not messages:
            return {}
        if silent:
            cmd += b".SILENT"

        data = await self._command_and_check(
            "store",
            join_message_ids(messages),
            cmd,
            seq_to_parenstr(flags),
            uid=True,
        )
        if silent:
            return None
        return self._filter_fetch_dict(parse_fetch_response(data), fetch_key)

    def _filter_fetch_dict(self, fetch_dict, key):
        return dict((msgid, data[key]) for msgid, data in fetch_dict.items())

    def _normalise_folder(self, folder_name):
        if isinstance(folder_name, bytes):
            folder_name = folder_name.decode("ascii")
        if self.folder_encode:
            folder_name = encode_utf7(folder_name)
        return _quote(folder_name)

    def _normalise_labels(self, labels):
        if isinstance(labels, (str, bytes)):
            labels = (labels,)
        return [_quote(encode_utf7(label)) for label in labels]

    @property
    def welcome(self):
        """Access the server greeting message."""
        try:
            return self._imap.welcome
        except AttributeError:
            pass

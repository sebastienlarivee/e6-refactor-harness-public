"""Host-authenticated Responses HTTP transport and incremental SSE framing.

The native CLI supplies its own complete payload and manages its context.
There is no generic gateway, token estimator, or local context admission here.
"""
from __future__ import annotations

from contextlib import contextmanager
from http.client import IncompleteRead
import io
from itertools import chain
import json
import re
import socket
import threading
import time
from typing import Any, Iterable, Mapping
from urllib import error, request

from .auth import AuthError, Credentials


class UpstreamError(RuntimeError):
    """Upstream status without response content or credentials."""

    def __init__(self, message: str, *, metadata: Any = None):
        super().__init__(message)
        self.metadata = safe_response_metadata(metadata)


class UpstreamPreparationError(UpstreamError):
    """Failure proved to occur before invoking the HTTP opener."""


_MEDIA_TYPES = {"text/event-stream", "application/json", "text/plain", "text/html",
                "application/octet-stream", "unclassified"}
_ERROR_CODES = {"invalid_request_error", "invalid_api_key", "invalid_value", "invalid_argument",
                "unsupported_parameter", "unsupported_value", "model_not_found", "permission_denied",
                "rate_limit_exceeded", "insufficient_quota", "authentication_error", "server_error",
                "context_length_exceeded", "request_too_large", "token_expired",
                "internal_error", "server_busy", "service_unavailable", "overloaded_error",
                "subscription_sharing_usage_unavailable", "subscription_sharing_user_unavailable",
                "subscription_sharing_usage_limit_exceeded"}
_CATEGORIES = {"http_success", "http_redirect", "http_client_error", "http_server_error",
               "non_sse_response", "connection_error", "transport_closed", "auth_preparation_error",
               "request_preparation_error", "malformed_stream", "stream_size_limit",
               "event_size_limit", "truncated_stream"}
_ERROR_DESCRIPTIONS = {"Unsupported parameter", "Invalid or missing instructions", "Model unavailable",
                       "Invalid or expired login", "Provider usage limit"}
_REQUEST_ID = re.compile(r"(?:req_[A-Za-z0-9]{8,128}|[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-"
                         r"[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12})\Z")
_CF_RAY = re.compile(r"[0-9a-fA-F]{16}(?:-[A-Z]{3})?\Z")
_MAX_BYTE_COUNT = 2**63 - 1
_MAX_DURATION = 365 * 24 * 3600
_EXCEPTION_TYPES = {"TimeoutError", "OSError", "BrokenPipeError", "ConnectionResetError",
                    "ConnectionAbortedError", "PermissionError", "IncompleteRead", "ValueError",
                    "TypeError", "AttributeError", "RuntimeError", "UpstreamError", "URLError",
                    "HTTPError", "LineTooLong", "RemoteDisconnected", "BadStatusLine", "SSLError"}
_HTTP_FUNCTIONS = {"read", "read1", "_read_chunked", "_read1_chunked", "_readinto_chunked",
                   "_get_chunk_left", "_read_next_chunk_size", "_safe_read"}
_READ_STAGES = {"chunk_body", "chunk_delimiter", "missing_or_invalid_chunk_size", "body", "unclassified"}
_ENCODINGS = {"absent", "identity", "chunked", "gzip", "deflate", "br", "zstd", "compress",
              "multiple", "unclassified"}


def _byte_count(value: Any) -> bool:
    return type(value) is int and 0 <= value <= _MAX_BYTE_COUNT


def _duration(value: Any) -> bool:
    return type(value) in {int, float} and 0 <= value <= _MAX_DURATION


def _seconds(start: float, end: float) -> float:
    return round(min(_MAX_DURATION, max(0, end - start)), 6)


def _safe_exception_fields(value: Any) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        return {}
    result = {}
    for key in ("error_type", "cause_type", "context_type"):
        name = value.get(key)
        if isinstance(name, str) and name in _EXCEPTION_TYPES | {"Exception"}:
            result[key] = name
    for key in ("expected_byte_count", "partial_byte_count"):
        count = value.get(key)
        if _byte_count(count) or (key == "expected_byte_count" and key in value and count is None):
            result[key] = count
    stage = value.get("http_read_stage")
    if isinstance(stage, str) and stage in _READ_STAGES:
        result["http_read_stage"] = stage
    names = value.get("http_functions")
    if isinstance(names, list) and len(names) <= len(_HTTP_FUNCTIONS):
        names = [name for name in names if isinstance(name, str) and name in _HTTP_FUNCTIONS]
        if names:
            result["http_functions"] = list(dict.fromkeys(names))
    return result


def safe_exception_metadata(exc: BaseException) -> dict[str, Any]:
    """Inspect only fixed class/function names, never traceback paths or locals."""
    def name(value):
        supplied = type(value).__name__
        return supplied if supplied in _EXCEPTION_TYPES else "Exception"
    details: dict[str, Any] = {"error_type": name(exc)}
    functions = []
    for key, linked in (("cause_type", exc.__cause__), ("context_type", exc.__context__)):
        if linked is not None:
            details[key] = name(linked)
    for linked in (exc, exc.__cause__, exc.__context__):
        frame = linked.__traceback__ if linked is not None else None
        # Bound traversal as well as output; no formatting of traceback data.
        for _ in range(32):
            if frame is None:
                break
            function = frame.tb_frame.f_code.co_name
            if frame.tb_frame.f_globals.get("__name__") == "http.client" and function in _HTTP_FUNCTIONS:
                if function not in functions:
                    functions.append(function)
            frame = frame.tb_next
    if functions:
        details["http_functions"] = functions
    if "_read_next_chunk_size" in functions:
        stage = "missing_or_invalid_chunk_size"
    elif "_get_chunk_left" in functions and "_safe_read" in functions:
        stage = "chunk_delimiter"
    elif any(function in functions for function in ("_read1_chunked", "_read_chunked", "_readinto_chunked")):
        stage = "chunk_body"
    elif "_safe_read" in functions:
        stage = "body"
    else:
        stage = "unclassified"
    details["http_read_stage"] = stage
    if isinstance(exc, IncompleteRead):
        details["expected_byte_count"] = exc.expected
        if isinstance(exc.partial, bytes):
            details["partial_byte_count"] = len(exc.partial)
    return _safe_exception_fields(details)


_REQUEST_FIELDS = {"model", "input", "instructions", "reasoning", "tools", "tool_choice",
                   "parallel_tool_calls", "stream", "store", "text", "temperature", "top_p",
                   "max_output_tokens", "prompt_cache_key", "prompt_cache_retention", "include",
                   "service_tier", "background"}


def safe_response_metadata(value: Any) -> dict[str, Any]:
    """Only bounded protocol facts may enter persistent upstream diagnostics."""
    if not isinstance(value, Mapping):
        return {}
    result = {}
    status = value.get("status")
    if type(status) is int and 100 <= status <= 599:
        result["status"] = status
    allowed = {"media_type": _MEDIA_TYPES, "category": _CATEGORIES, "code": _ERROR_CODES,
               "type": _ERROR_CODES, "param": _REQUEST_FIELDS, "message": _ERROR_DESCRIPTIONS}
    for key, choices in allowed.items():
        supplied = value.get(key)
        if isinstance(supplied, str) and len(supplied) <= 128 and supplied in choices:
            result[key] = supplied
    supplied = value.get("request_id")
    if isinstance(supplied, str) and len(supplied) <= 132 and _REQUEST_ID.fullmatch(supplied):
        result["request_id"] = supplied
    supplied = value.get("cf_ray")
    if isinstance(supplied, str) and len(supplied) <= 20 and _CF_RAY.fullmatch(supplied):
        result["cf_ray"] = supplied
    if type(value.get("sse_prefix")) is bool:
        result["sse_prefix"] = value["sse_prefix"]
    supplied = value.get("framing")
    if isinstance(supplied, Mapping):
        framing = {}
        if type(supplied.get("chunked")) is bool:
            framing["chunked"] = supplied["chunked"]
        version = supplied.get("http_version")
        if isinstance(version, str) and version in {"1.0", "1.1", "2"}:
            framing["http_version"] = version
        if _byte_count(supplied.get("content_length")):
            framing["content_length"] = supplied["content_length"]
        state = supplied.get("content_length_state")
        if isinstance(state, str) and state in {"absent", "valid", "invalid"}:
            framing["content_length_state"] = state
        for key in ("transfer_encoding", "content_encoding"):
            encoding = supplied.get(key)
            if isinstance(encoding, str) and encoding in _ENCODINGS:
                framing[key] = encoding
        if framing:
            result["framing"] = framing
    supplied = value.get("timing")
    if isinstance(supplied, Mapping):
        timing = {key: supplied[key] for key in ("elapsed_seconds", "headers_seconds", "first_byte_seconds",
                  "last_byte_seconds", "last_byte_age_seconds") if _duration(supplied.get(key))}
        if timing:
            result["timing"] = timing
    supplied = value.get("transport_close")
    if isinstance(supplied, Mapping) and type(supplied.get("begun")) is bool:
        result["transport_close"] = {"begun": supplied["begun"]}
        if _duration(supplied.get("age_seconds")):
            result["transport_close"]["age_seconds"] = supplied["age_seconds"]
    supplied = value.get("stream_read")
    if isinstance(supplied, Mapping):
        stream_read = {}
        if type(supplied.get("eof_seen")) is bool:
            stream_read["eof_seen"] = supplied["eof_seen"]
        if _byte_count(supplied.get("content_length_remaining")):
            stream_read["content_length_remaining"] = supplied["content_length_remaining"]
        if stream_read:
            result["stream_read"] = stream_read
    read_failure = _safe_exception_fields(value.get("read_failure"))
    if read_failure:
        result["read_failure"] = read_failure
    supplied = value.get("error_body")
    if isinstance(supplied, Mapping):
        body = {}
        if _byte_count(supplied.get("observed_byte_count")):
            body["observed_byte_count"] = supplied["observed_byte_count"]
        allowed_body = {"read_state": {"complete", "limit", "failure"},
                        "json_shape": {"object", "array", "string", "number", "boolean", "null", "invalid", "not_parsed"},
                        "classification": {"empty_body", "json_error_document", "json_document", "plaintext_http_503",
                                           "non_json", "body_read_failure"}}
        for key, choices in allowed_body.items():
            field = supplied.get(key)
            if isinstance(field, str) and field in choices:
                body[key] = field
        if body:
            result["error_body"] = body
    return result


def _http_metadata(status: Any, headers: Any, response: Any = None) -> dict[str, Any]:
    details = {"status": status}
    if type(status) is int and 200 <= status <= 599:
        details["category"] = ("http_success" if status < 300 else "http_redirect" if status < 400
                               else "http_client_error" if status < 500 else "http_server_error")
    if headers is not None:
        framing = {}
        length = headers.get("Content-Length")
        framing["content_length_state"] = "absent" if length is None else "invalid"
        if isinstance(length, str) and len(length) <= 19 and length.isascii() and length.isdigit():
            count = int(length)
            if _byte_count(count):
                framing.update(content_length=count, content_length_state="valid")
        for header, field in (("Transfer-Encoding", "transfer_encoding"), ("Content-Encoding", "content_encoding")):
            encoding = headers.get(header)
            if encoding is None:
                framing[field] = "absent"
            elif isinstance(encoding, str) and len(encoding) <= 128:
                parts = [part.strip().lower() for part in encoding.split(",")]
                framing[field] = (parts[0] if len(parts) == 1 and parts[0] in _ENCODINGS - {"absent", "multiple", "unclassified"}
                                  else "multiple" if len(parts) > 1 and all(part in _ENCODINGS - {"absent", "multiple", "unclassified"} for part in parts)
                                  else "unclassified")
            else:
                framing[field] = "unclassified"
        chunked = getattr(response, "chunked", None)
        if type(chunked) is bool:
            framing["chunked"] = chunked
        version = getattr(response, "version", None)
        if type(version) is int and version in {10, 11, 20}:
            framing["http_version"] = {10: "1.0", 11: "1.1", 20: "2"}[version]
        details["framing"] = framing
        if hasattr(headers, "get_content_type"):
            media = headers.get_content_type()
        else:
            supplied = headers.get("Content-Type")
            media = supplied.split(";", 1)[0].strip().lower() if isinstance(supplied, str) else None
        details["media_type"] = media if isinstance(media, str) and media in _MEDIA_TYPES else "unclassified"
        details["cf_ray"] = headers.get("cf-ray")
        for name in ("x-request-id", "request-id", "openai-request-id"):
            identifier = headers.get(name)
            if safe_response_metadata({"request_id": identifier}):
                details["request_id"] = identifier
                break
    return safe_response_metadata(details)


def _safe_upstream_details(exc: error.HTTPError, credentials: Credentials) -> dict[str, Any]:
    """Classify a bounded error document without recording arbitrary messages.

    Provider messages can echo prompt text, schemas or secret values. Only
    known protocol field names, known error categories and fixed descriptions
    leave this function; unrecognized prose is deliberately not retained.
    """
    details = _http_metadata(exc.code, exc.headers, exc.fp)
    body: dict[str, Any] = {"observed_byte_count": 0, "read_state": "failure", "json_shape": "not_parsed",
                            "classification": "body_read_failure"}
    try:
        raw = exc.read(65536)
    except (OSError, ValueError, UnicodeError, RecursionError, IncompleteRead) as read_error:
        if isinstance(read_error, IncompleteRead) and isinstance(read_error.partial, bytes):
            body["observed_byte_count"] = len(read_error.partial)
        details["read_failure"] = safe_exception_metadata(read_error)
        document = None
    else:
        body["observed_byte_count"] = len(raw)
        remaining = getattr(exc.fp, "length", None)
        body["read_state"] = "limit" if len(raw) == 65536 else "failure" if _byte_count(remaining) and remaining > 0 else "complete"
        try:
            document = json.loads(raw)
        except (ValueError, UnicodeError, RecursionError):
            document = None
            body["json_shape"] = "invalid"
            body["classification"] = ("empty_body" if not raw else "plaintext_http_503"
                                      if exc.code == 503 and details.get("media_type") == "text/plain" else "non_json")
        else:
            body["json_shape"] = ("object" if isinstance(document, dict) else "array" if isinstance(document, list)
                                  else "string" if isinstance(document, str) else "boolean" if type(document) is bool
                                  else "null" if document is None else "number")
            body["classification"] = "json_error_document" if isinstance(document, dict) and "error" in document else "json_document"
        if body["read_state"] == "failure":
            body["classification"] = "body_read_failure"
    details["error_body"] = body
    if isinstance(document, dict):
        supplied = document.get("error", document)
        if isinstance(supplied, dict):
            for key in ("code", "type"):
                value = supplied.get(key)
                if isinstance(value, str) and value in _ERROR_CODES:
                    details[key] = value
            param = supplied.get("param")
            if isinstance(param, str) and param in _REQUEST_FIELDS:
                details["param"] = param
            message = supplied.get("message", supplied.get("detail"))
        else:
            message = supplied
        if not isinstance(message, str):
            message = document.get("detail")
        if isinstance(message, str):
            message = credentials.redact(message)
            if re.search(r"(unsupported|unknown|unrecognized)\s+(parameter|field)", message, re.I):
                details["message"] = "Unsupported parameter"
            elif re.search(r"instructions.{0,20}(required|must|missing)", message, re.I):
                details["message"] = "Invalid or missing instructions"
            elif re.search(r"model.{0,50}(not found|not supported|unsupported|does not exist|not available)|(?:unknown|invalid|unsupported)\s+model", message, re.I):
                details["message"] = "Model unavailable"
            elif re.search(r"(token|credential).{0,30}(expired|invalid)", message, re.I):
                details["message"] = "Invalid or expired login"
            elif re.search(r"(usage limit|rate limit|quota)", message, re.I):
                details["message"] = "Provider usage limit"
            # Only select a recognized quoted field, never untrusted prose.
            match = re.search(r"(?:parameter|field)\s*:?\s*['\"]?([a-z_]+)", message, re.I)
            if match and match.group(1) in _REQUEST_FIELDS:
                details.setdefault("param", match.group(1))
    return safe_response_metadata(details)


def _safe_upstream_error(exc: error.HTTPError, credentials: Credentials) -> str:
    return "Upstream rejected the request " + json.dumps(
        _safe_upstream_details(exc, credentials), sort_keys=True, separators=(",", ":"))


class _NoRedirect(request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class ResponsesTransport:
    """Fixed-endpoint urllib transport; authentication stays in the host.

    There are no automatic retries, redirects, cookies or worker-controlled
    headers. A rejected request retains its reservation as unknown usage.
    """
    def __init__(self, credentials: Credentials):
        self.credentials = credentials
        self.supports_output_cap = credentials.supports_output_cap
        self.last_response_metadata: dict[str, Any] = {}
        self._opener = request.build_opener(_NoRedirect())
        self._response_lock = threading.Lock()
        self._responses: set[Any] = set()
        self._closed = False
        self._close_started: float | None = None
        self._request_started: float | None = None
        self._headers_at: float | None = None
        self._first_byte_at: float | None = None
        self._last_byte_at: float | None = None
        self._request_active = False

    def _snapshot_locked(self, now: float) -> dict[str, Any]:
        # Sample local shutdown before copying response metadata. The same
        # lock publishes close-begun before any socket shutdown can interrupt
        # a reader; it is never held across network reads or shutdown calls.
        closing: dict[str, Any] = {"begun": self._closed}
        if self._close_started is not None:
            closing["age_seconds"] = _seconds(self._close_started, now)
        details = safe_response_metadata(self.last_response_metadata)
        details["transport_close"] = closing
        if self._request_started is not None:
            timing = {"elapsed_seconds": _seconds(self._request_started, now)}
            for field, observed in (("headers_seconds", self._headers_at), ("first_byte_seconds", self._first_byte_at),
                                    ("last_byte_seconds", self._last_byte_at)):
                if observed is not None:
                    timing[field] = _seconds(self._request_started, observed)
            if self._last_byte_at is not None:
                timing["last_byte_age_seconds"] = _seconds(self._last_byte_at, now)
            details["timing"] = timing
        return details

    def diagnostic_snapshot(self, *, active_only: bool = False) -> dict[str, Any]:
        with self._response_lock:
            details = self._snapshot_locked(time.monotonic())
            # A relay marker can precede entry into this context. In that
            # interval, completed request metadata belongs to a prior call.
            if active_only and not self._request_active:
                return {"transport_close": details["transport_close"]}
            return details

    def _metadata(self, details: Mapping[str, Any], *, headers: bool = False, bytes_observed: int = 0) -> None:
        now = time.monotonic()
        with self._response_lock:
            if headers:
                self._headers_at = now
            if bytes_observed > 0:
                if self._first_byte_at is None:
                    self._first_byte_at = now
                self._last_byte_at = now
            self.last_response_metadata.update(safe_response_metadata(details))
            self.last_response_metadata = self._snapshot_locked(now)

    def _read_one(self, response: Any, size: int) -> bytes:
        try:
            chunk = response.read1(size)
        except Exception as exc:
            details = {"read_failure": safe_exception_metadata(exc)}
            remaining = getattr(response, "length", None)
            if _byte_count(remaining):
                details["stream_read"] = {"eof_seen": False, "content_length_remaining": remaining}
            self._metadata(details)
            raise
        if size == 0:
            # The existing bounded prefix loop can request zero bytes. An
            # empty zero-byte read says nothing about upstream EOF.
            self._metadata({})
            return chunk
        # Empty read return is an observed EOF. Context exit or fp=None is
        # deliberately insufficient: terminal events stop consumption early,
        # and malformed chunk-size parsing itself can close the HTTP file.
        state = {"eof_seen": not chunk}
        remaining = getattr(response, "length", None)
        if _byte_count(remaining):
            state["content_length_remaining"] = remaining
        self._metadata({"stream_read": state}, bytes_observed=len(chunk))
        return chunk

    def close(self) -> None:
        with self._response_lock:
            if self._close_started is None:
                self._close_started = time.monotonic()
            self._closed = True
            responses = list(self._responses)
            self.last_response_metadata = self._snapshot_locked(time.monotonic())
        for response in responses:
            try:
                raw = getattr(getattr(response, "fp", None), "raw", None)
                upstream_socket = getattr(raw, "_sock", None)
                if upstream_socket is not None:
                    upstream_socket.shutdown(socket.SHUT_RDWR)
                # The reader owns response.close(). Closing its buffered file
                # here can clear HTTPResponse.fp during a chunked read1 and
                # raise AttributeError instead of interrupting the socket read.
            except OSError:
                pass


    @contextmanager
    def open_response(self, payload: Mapping[str, Any], timeout_seconds: float | None):
        with self._response_lock:
            self.last_response_metadata = {}
            self._request_started = time.monotonic()
            self._headers_at = self._first_byte_at = self._last_byte_at = None
            self._request_active = not self._closed
            if self._closed:
                self.last_response_metadata = {"category": "transport_closed"}
                self.last_response_metadata = self._snapshot_locked(time.monotonic())
                raise UpstreamPreparationError("Broker transport is closed", metadata=self.last_response_metadata)
        try:
            headers = self.credentials.headers()
            body = json.dumps(payload, ensure_ascii=False, separators=(",", ":"), allow_nan=False).encode("utf-8")
            req = request.Request(self.credentials.endpoint, data=body, headers=headers, method="POST")
        except Exception as exc:
            category = "auth_preparation_error" if isinstance(exc, AuthError) else "request_preparation_error"
            self._metadata({"category": category})
            with self._response_lock:
                self._request_active = False
            message = ("Upstream authentication failed before HTTP dispatch" if isinstance(exc, AuthError)
                       else "Upstream request preparation failed before HTTP dispatch")
            raise UpstreamPreparationError(message, metadata=self.last_response_metadata) from None
        started = time.monotonic()
        response = None
        try:
            response = self._opener.open(req, timeout=timeout_seconds)
            self._metadata({**_http_metadata(response.status, response.headers, response), "stream_read": {"eof_seen": False}}, headers=True)
            with self._response_lock:
                if self._closed:
                    raise UpstreamError("Broker transport is closed", metadata={**self._snapshot_locked(time.monotonic()), "category": "transport_closed"})
                self._responses.add(response)
            media = response.headers.get_content_type()
            first = b""
            if media != "text/event-stream":
                first = self._read_one(response, 65536)
                while len(first.lstrip()) < 6 and first:
                    extra = self._read_one(response, 65536 - len(first))
                    if not extra:
                        break
                    first += extra
                sse_prefix = first.lstrip().startswith((b"data:", b"event:", b":"))
                self._metadata({"sse_prefix": sse_prefix})
                if not sse_prefix:
                    pseudo_error = error.HTTPError(self.credentials.endpoint, response.status, "Non-SSE response", response.headers, io.BytesIO(first))
                    details = _safe_upstream_details(pseudo_error, self.credentials)
                    # These bytes are only the already inspected prefix, not
                    # the complete upstream error body or additional reads.
                    details.pop("error_body", None)
                    details.pop("framing", None)
                    self._metadata({**details, "category": "non_sse_response"})
                    reason = "Upstream rejected the request " + json.dumps(details, sort_keys=True, separators=(",", ":"))
                    raise UpstreamError("Upstream did not return SSE; " + reason + "; media_type=" + self.last_response_metadata["media_type"],
                                        metadata=self.last_response_metadata)

            def chunks():
                while True:
                    with self._response_lock:
                        if self._closed:
                            raise UpstreamError("Broker transport is closed", metadata={**self._snapshot_locked(time.monotonic()), "category": "transport_closed"})
                    remaining = (timeout_seconds - (time.monotonic() - started)
                                 if timeout_seconds is not None else None)
                    if remaining is not None and remaining <= 0:
                        raise TimeoutError("Upstream deadline exceeded")
                    # HTTPResponse.read1 avoids waiting for a large full chunk.
                    # Set each socket read's bound to the remaining total time.
                    raw = getattr(getattr(response, "fp", None), "raw", None)
                    upstream_socket = getattr(raw, "_sock", None)
                    if upstream_socket is not None:
                        upstream_socket.settimeout(remaining)
                    chunk = self._read_one(response, 65536)
                    if not chunk:
                        return
                    yield chunk

            # Prime's provider decodes SSE even when the server labels it plain
            # text or omits the header. The prefix and bounded decoder validate
            # framing while preserving the first bytes already inspected.
            yield chain([first], chunks()) if first else chunks()
        except error.HTTPError as exc:
            self._metadata(_http_metadata(exc.code, exc.headers, exc.fp), headers=True)
            try:
                details = _safe_upstream_details(exc, self.credentials)
                self._metadata(details, bytes_observed=details.get("error_body", {}).get("observed_byte_count", 0))
            finally:
                exc.close()
            reason = "Upstream rejected the request " + json.dumps(
                self.last_response_metadata, sort_keys=True, separators=(",", ":"))
            raise UpstreamError(reason, metadata=self.last_response_metadata) from None
        except error.URLError:
            self._metadata({"category": "connection_error"})
            raise UpstreamError("Upstream connection failed", metadata=self.last_response_metadata) from None
        finally:
            with self._response_lock:
                self._request_active = False
            if response is not None:
                with self._response_lock:
                    self._responses.discard(response)
                response.close()


def sse_events(chunks: Iterable[bytes], *, max_event_bytes: int | None = 2 * 1024 * 1024,
               max_stream_bytes: int | None = 64 * 1024 * 1024):
    """Incremental SSE decoder; callers may explicitly omit byte bounds."""
    pending = bytearray()
    event = []
    event_size = 0
    total = 0
    for chunk in chunks:
        if not isinstance(chunk, bytes):
            raise UpstreamError("Malformed upstream stream", metadata={"category": "malformed_stream"})
        total += len(chunk)
        if max_stream_bytes is not None and total > max_stream_bytes:
            raise UpstreamError("Upstream stream exceeded size limit", metadata={"category": "stream_size_limit"})
        pending.extend(chunk)
        while b"\n" in pending:
            line, _, tail = pending.partition(b"\n")
            pending = bytearray(tail)
            line = bytes(line).rstrip(b"\r")
            event_size += len(line) + 1
            if max_event_bytes is not None and event_size > max_event_bytes:
                raise UpstreamError("Upstream SSE event exceeded size limit", metadata={"category": "event_size_limit"})
            if line:
                event.append(line)
                continue
            if event:
                data = b"\n".join(line[5:].lstrip(b" ") for line in event if line.startswith(b"data:"))
                if data:
                    yield data
            event = []
            event_size = 0
        if max_event_bytes is not None and len(pending) + event_size > max_event_bytes:
            raise UpstreamError("Upstream SSE event exceeded size limit", metadata={"category": "event_size_limit"})
    if pending or event:
        raise UpstreamError("Upstream SSE stream ended mid-event", metadata={"category": "truncated_stream"})

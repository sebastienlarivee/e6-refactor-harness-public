"""Host-only Sign in with ChatGPT auth via the pinned Pi provider SDK.

The helper owns native token refresh and persistence; secrets travel only through
subprocess pipes and in-memory HTTP headers. Workers get the relay's local token.
No model inference, credential migration, interactive login or API-key fallback.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import json
import math
from pathlib import Path
import re
import subprocess
import time
from typing import Any, Mapping

from transport.auth import AuthError
from transport.responses import ResponsesTransport

PUBLIC_BASE = "https://api.openai.com/v1"
PUBLIC_ENDPOINT = PUBLIC_BASE + "/responses"
DIRECT_SCOPE = "chatgpt.tokens.use.direct"
HEADER_NAME = re.compile(r"^[!#$%&'*+.^_`|~0-9a-zA-Z-]+$")
PI_METADATA_HEADERS = {"session_id", "x-client-request-id"}


def _header_value(value: Any) -> str:
    if (not isinstance(value, str) or not value or len(value) > 65536
            or any(ord(char) < 32 or ord(char) == 127 for char in value)):
        raise AuthError("Pi SDK returned invalid request authentication")
    return value


@dataclass(repr=False)
class PiCredentials:
    """Resolved native auth, retained only in host memory."""
    auth_headers: dict[str, str] = field(repr=False)
    expires_at: float
    scopes: tuple[str, ...]
    kind: str = "pi_oauth"
    source: str = "pi-native-sdk"
    endpoint: str = PUBLIC_ENDPOINT
    supports_output_cap: bool = False
    native_headers: dict[str, str] = field(default_factory=dict, repr=False)

    def __repr__(self):
        return "PiCredentials(kind='pi_oauth', source='pi-native-sdk')"

    def headers(self) -> dict[str, str]:
        if self.expires_at <= time.time() + 30:
            raise AuthError("Pi OAuth token validity expired before dispatch")
        result = {"Content-Type": "application/json", "Accept": "text/event-stream", **self.auth_headers}
        # Provider-resolved headers always take precedence over worker metadata.
        occupied = {key.lower() for key in result}
        result.update({key: value for key, value in self.native_headers.items() if key.lower() not in occupied})
        return result

    def public_status(self) -> dict[str, Any]:
        return {"configured": True, "kind": self.kind, "source": self.source,
                "endpoint": self.endpoint, "expires_at": self.expires_at,
                "supports_output_cap": False}

    def redact(self, message: object) -> str:
        result = str(message)
        for value in self.auth_headers.values():
            result = result.replace(value, "[redacted]")
            if value.startswith("Bearer "):
                result = result.replace(value[7:], "[redacted]")
        return result


def _resolved_credentials(document: Any, *, now: float | None = None) -> PiCredentials:
    """Validate private helper output without including it in diagnostics."""
    current = time.time() if now is None else now
    if (not isinstance(document, dict) or document.get("kind") != "pi_oauth"
            or document.get("base_url") != PUBLIC_BASE):
        raise AuthError("Pi SDK did not resolve public Responses OAuth authentication")
    scopes = document.get("scopes")
    if (not isinstance(scopes, list) or any(not isinstance(scope, str) for scope in scopes)
            or DIRECT_SCOPE not in scopes):
        raise AuthError("Pi OAuth grant lacks direct token-sharing scope")
    expires = document.get("expires_at")
    if (isinstance(expires, bool) or not isinstance(expires, (int, float))
            or not math.isfinite(expires) or expires <= current + 30):
        raise AuthError("Pi SDK resolved an invalid or expired OAuth token")
    auth = document.get("auth")
    if not isinstance(auth, dict) or auth.get("baseUrl", PUBLIC_BASE) != PUBLIC_BASE:
        raise AuthError("Pi SDK resolved an unsupported request endpoint")
    supplied = auth.get("headers", {})
    if not isinstance(supplied, dict):
        raise AuthError("Pi SDK returned invalid request authentication")
    headers: dict[str, str] = {}
    for name, value in supplied.items():
        if not isinstance(name, str) or not HEADER_NAME.fullmatch(name):
            raise AuthError("Pi SDK returned invalid request authentication")
        if value is None:  # Native ProviderHeaders null means remove a default.
            continue
        if name.lower() in {key.lower() for key in headers}:
            raise AuthError("Pi SDK returned duplicate authentication headers")
        if name.lower() in {"host", "content-length", "transfer-encoding", "connection"}:
            raise AuthError("Pi SDK returned unsupported transport headers")
        headers[name] = _header_value(value)
    authorization = next((value for name, value in headers.items() if name.lower() == "authorization"), None)
    if authorization is not None and (not authorization.startswith("Bearer ")
            or authorization.startswith("Bearer sk-")):
        raise AuthError("Pi SDK did not resolve bearer OAuth authentication")
    api_key = auth.get("apiKey")
    if api_key is not None:
        access = _header_value(api_key)
        if access.startswith("sk-"):
            raise AuthError("Pi backend requires OAuth rather than an API key")
        if authorization is None:
            headers["Authorization"] = "Bearer " + access
    elif authorization is None or not authorization.startswith("Bearer ") or authorization.startswith("Bearer sk-"):
        raise AuthError("Pi SDK did not resolve bearer OAuth authentication")
    return PiCredentials(headers, float(expires), tuple(scopes))


class PiAuthResolver:
    def __init__(self, auth_path: str | Path, runtime: Mapping[str, Any]):
        self.auth_path = Path(auth_path).expanduser().resolve()
        try:
            self.node = str(runtime["pi_node"])
            self.package = str(runtime["pi_package"])
        except (KeyError, TypeError):
            raise AuthError("Pinned Pi runtime is required for native OAuth resolution") from None
        self.version = str(runtime.get("pi_version", runtime.get("pi_release", "1.1.0")))
        # A release field can be a filesystem path; the version is independently pinned.
        if "/" in self.version or "\\" in self.version:
            self.version = "1.1.0"
        self.helper = Path(__file__).with_suffix(".mjs")

    def resolve(self, timeout: float | None = None) -> PiCredentials:
        # Native auth has bounded lock/refresh operations and a helper signal.
        # Do not kill the process on timeout: once refresh starts, Pi must finish
        # persisting its rotated token even if the request deadline has elapsed.
        try:
            result = subprocess.run([self.node, str(self.helper), self.package,
                                     str(self.auth_path), self.version],
                                    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, check=False)
        except (OSError, subprocess.SubprocessError):
            raise AuthError("Pi native OAuth resolver could not complete") from None
        if result.returncode != 0:
            raise AuthError("Pi native OAuth resolution failed; existing login could not be resolved")
        try:
            document = json.loads(result.stdout)
        except (ValueError, UnicodeError, RecursionError):
            raise AuthError("Pi native OAuth resolver returned an invalid result") from None
        return _resolved_credentials(document)


class PiResponsesTransport(ResponsesTransport):
    """Public Responses transport with native auth prepared before dispatch."""
    def __init__(self, resolver: PiAuthResolver):
        self.resolver = resolver
        # Resolve only at pre-dispatch, after recording the durable zero marker.
        super().__init__(PiCredentials({}, 0, ()))
        self._native_headers: dict[str, str] = {}

    def set_native_headers(self, supplied) -> None:
        native = {}
        for name in PI_METADATA_HEADERS:
            values = supplied.get_all(name, []) if hasattr(supplied, "get_all") else [
                value for key, value in supplied.items() if key.lower() == name]
            if not values:
                continue
            if len(values) != 1:
                raise AuthError("Invalid Pi request metadata header")
            native[name] = _header_value(values[0])
        self._native_headers = native

    def prepare_request(self, timeout: float | None) -> None:
        self.credentials = self.resolver.resolve(timeout)
        self.credentials.native_headers = dict(self._native_headers)

    def prepare_payload(self, payload):
        result = dict(payload)
        result.update(stream=True, store=False, service_tier="default")
        for key in ("max_output_tokens", "prompt_cache_retention", "prompt_cache_options", "temperature"):
            result.pop(key, None)
        return result

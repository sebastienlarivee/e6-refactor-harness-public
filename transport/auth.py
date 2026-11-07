"""Host-only OpenAI credentials. Workers receive a broker token, never these values.

Prime's native ``openai-codex`` login is preferred when explicitly supplied.
An explicitly supplied Codex auth file is also supported. Loading never refreshes
or modifies a personal credential file: an expired login fails before a request.
Snapshot loading is retained for canaries; the relay's adapter rereads the same
source so an externally renewed login can be used by future requests.
"""
from __future__ import annotations

import base64
from dataclasses import dataclass, field
import json
import math
import os
from pathlib import Path
import threading
import time
from typing import Mapping


class AuthError(RuntimeError):
    """A safe, credential-free authentication diagnostic."""


def _jwt_claims(token: str) -> dict:
    try:
        parts = token.split(".")
        if len(parts) != 3:
            return {}
        raw = base64.urlsafe_b64decode(parts[1] + "=" * (-len(parts[1]) % 4))
        claims = json.loads(raw)
        return claims if isinstance(claims, dict) else {}
    except (ValueError, UnicodeError):
        return {}


def _header_value(value: object, label: str) -> str:
    if not isinstance(value, str) or not value or len(value) > 65536 or any(ord(c) < 32 or ord(c) == 127 for c in value):
        raise AuthError(f"Invalid {label} in configured credential source")
    return value


@dataclass(frozen=True)
class Credentials:
    kind: str
    access_token: str = field(repr=False)
    account_id: str | None = field(default=None, repr=False)
    expires_at: float | None = None
    source: str = "explicit"

    @property
    def endpoint(self) -> str:
        return ("https://chatgpt.com/backend-api/codex/responses" if self.kind == "codex_oauth"
                else "https://api.openai.com/v1/responses")

    @property
    def supports_output_cap(self) -> bool:
        # Prime's native Codex provider omits max_output_tokens. The backend does
        # not support that field, so reservations must use the model's full cap.
        return self.kind == "api_key"

    def ensure_valid(self, now: float | None = None) -> None:
        if self.kind not in {"codex_oauth", "api_key"}:
            raise AuthError("Unsupported credential kind")
        _header_value(self.access_token, "access token")
        if self.kind == "codex_oauth":
            _header_value(self.account_id, "ChatGPT account ID")
        if self.expires_at is not None and self.expires_at <= (time.time() if now is None else now) + 30:
            raise AuthError("Configured OpenAI login has expired; sign in again with Prime or Codex")

    def headers(self) -> dict[str, str]:
        self.ensure_valid()
        headers = {"Authorization": f"Bearer {self.access_token}", "Content-Type": "application/json",
                   "Accept": "text/event-stream", "User-Agent": "prime-lean-harness/1"}
        if self.kind == "codex_oauth":
            headers.update({"ChatGPT-Account-Id": self.account_id or "", "originator": "pi",
                            "OpenAI-Beta": "responses=experimental"})
        return headers

    def public_status(self) -> dict:
        return {"configured": True, "kind": self.kind, "source": self.source,
                "supports_output_cap": self.supports_output_cap, "expires_at": self.expires_at}

    def redact(self, message: object) -> str:
        result = str(message)
        for secret in (self.access_token, self.account_id):
            if secret:
                result = result.replace(secret, "[redacted]")
        return result


def _document(path: str | Path) -> dict:
    try:
        source = Path(path)
        if source.stat().st_size > 1024 * 1024:
            raise AuthError("Configured auth file is too large")
        document = json.loads(source.read_text(encoding="utf-8-sig"))
    except AuthError:
        raise
    except (OSError, ValueError, UnicodeError):
        raise AuthError("Cannot read the explicitly configured OpenAI auth file") from None
    if not isinstance(document, dict):
        raise AuthError("Configured auth file must contain a JSON object")
    return document


def _oauth(access: object, account: object, expiry: object, source: str, now: float) -> Credentials:
    token = _header_value(access, "access token")
    claims = _jwt_claims(token)
    claim_account = claims.get("https://api.openai.com/auth", {})
    if not isinstance(claim_account, dict):
        claim_account = {}
    account = account or claim_account.get("chatgpt_account_id")
    account = _header_value(account, "ChatGPT account ID")
    if len(account) > 512:
        raise AuthError("Invalid ChatGPT account ID in configured credential source")
    expiries = []
    for value in (expiry, claims.get("exp")):
        if value is None:
            continue
        if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or value <= 0:
            raise AuthError("Invalid expiry in configured OpenAI login")
        # Prime stores epoch milliseconds, Codex JWT exp uses epoch seconds.
        expiries.append(float(value) / 1000 if value > 100_000_000_000 else float(value))
    if not expiries:
        raise AuthError("Configured OpenAI login has no verifiable expiry; sign in again")
    credential = Credentials("codex_oauth", token, account, min(expiries), source)
    credential.ensure_valid(now)
    return credential


def load_credentials(*, prime_auth_path: str | Path | None = None, codex_auth_path: str | Path | None = None,
                     api_key_env: str = "OPENAI_API_KEY", environ: Mapping[str, str] | None = None,
                     now: float | None = None) -> Credentials:
    """Load only explicit files or the named API-key variable, in that order.

    No ambient auth-file discovery and no fallback from a malformed or expired
    explicitly selected file. This makes the credential choice reproducible.
    """
    current = time.time() if now is None else now
    if prime_auth_path is not None:
        document = _document(prime_auth_path)
        entry = document.get("openai-codex")
        if not isinstance(entry, dict) or entry.get("type") != "oauth":
            raise AuthError("Configured Prime auth file lacks an openai-codex OAuth login")
        return _oauth(entry.get("access"), entry.get("accountId"), entry.get("expires"), "prime-auth-file", current)
    if codex_auth_path is not None:
        document = _document(codex_auth_path)
        tokens = document.get("tokens")
        if isinstance(tokens, dict):
            return _oauth(tokens.get("access_token"), tokens.get("account_id"), None, "codex-auth-file", current)
        key = document.get("OPENAI_API_KEY")
        if key:
            return Credentials("api_key", _header_value(key, "API key"), source="codex-auth-file")
        raise AuthError("Configured Codex auth file lacks usable OpenAI credentials")
    environment = os.environ if environ is None else environ
    key = environment.get(api_key_env)
    if key:
        return Credentials("api_key", _header_value(key, "API key"), source="api-key-environment")
    raise AuthError("Configure Prime openai-codex auth, an authorized Codex auth file, or OPENAI_API_KEY")


class ReloadableCredentials:
    """Read the selected host source again before dispatch, retaining its identity.

    This is a read-only adapter: an external authorized login may replace a file,
    but the relay never refreshes tokens, switches accounts, or retries requests.
    The original kind and endpoint also keep payload capabilities stable.
    """

    def __init__(self, initial: Credentials, options: dict):
        self._initial = initial
        self._current = initial
        self._options = dict(options)
        self._lock = threading.RLock()
        self._redactions = {value for value in (initial.access_token, initial.account_id) if value}
        self._validate_account(initial)

    @staticmethod
    def _validate_account(credentials: Credentials) -> None:
        if credentials.kind != "codex_oauth":
            return
        claim = _jwt_claims(credentials.access_token).get("https://api.openai.com/auth")
        if isinstance(claim, dict) and "chatgpt_account_id" in claim:
            account = _header_value(claim["chatgpt_account_id"], "ChatGPT account ID")
            if account != credentials.account_id:
                raise AuthError("Configured OpenAI login account does not match its access token")

    @property
    def kind(self) -> str:
        return self._initial.kind

    @property
    def account_id(self) -> str | None:
        return self._initial.account_id

    @property
    def endpoint(self) -> str:
        return self._initial.endpoint

    @property
    def source(self) -> str:
        return self._initial.source

    @property
    def supports_output_cap(self) -> bool:
        return self._initial.supports_output_cap

    @property
    def access_token(self) -> str:
        with self._lock:
            return self._current.access_token

    @property
    def expires_at(self) -> float | None:
        with self._lock:
            return self._current.expires_at

    def _reload(self, now: float | None = None) -> Credentials:
        with self._lock:
            current = load_credentials(**self._options, now=now)
            if current.kind != self.kind or current.endpoint != self.endpoint or current.source != self.source:
                raise AuthError("Configured OpenAI credential kind or source changed during the run")
            self._validate_account(current)
            if current.account_id != self.account_id:
                raise AuthError("Configured OpenAI credential account changed during the run")
            current.ensure_valid(now)
            self._current = current
            self._redactions.update(value for value in (current.access_token, current.account_id) if value)
            return current

    def ensure_valid(self, now: float | None = None) -> None:
        self._reload(now)

    def headers(self) -> dict[str, str]:
        # Use one loaded snapshot to build all authentication headers. Stable
        # endpoint/capability properties cannot switch while a request is built.
        return self._reload().headers()

    def public_status(self) -> dict:
        with self._lock:
            return self._current.public_status()

    def redact(self, message: object) -> str:
        with self._lock:
            result = str(message)
            for secret in sorted(self._redactions, key=len, reverse=True):
                result = result.replace(secret, "[redacted]")
            return result


def load_reloadable_credentials(*, prime_auth_path: str | Path | None = None,
                               codex_auth_path: str | Path | None = None,
                               api_key_env: str = "OPENAI_API_KEY", environ: Mapping[str, str] | None = None,
                               now: float | None = None) -> ReloadableCredentials:
    """Validate once, then reload the same explicit source for future dispatches.

    ``load_credentials`` retains its snapshot semantics for canaries. ``now``
    controls initial validation only; dispatches use the current clock. Relative
    file paths are anchored here so a later working-directory change cannot
    choose a different source. File errors never fall back to environment keys.
    """
    options = {"prime_auth_path": Path(prime_auth_path).absolute() if prime_auth_path is not None else None,
               "codex_auth_path": Path(codex_auth_path).absolute() if codex_auth_path is not None else None,
               "api_key_env": api_key_env, "environ": environ}
    initial = load_credentials(**options, now=now)
    initial.ensure_valid(now)
    return ReloadableCredentials(initial, options)

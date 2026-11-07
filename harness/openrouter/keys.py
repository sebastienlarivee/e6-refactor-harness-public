"""Explicit host credential lifecycle; importing this module never contacts a provider.

The store belongs outside every run/agent/repository tree and must never be
bundled. Its API returns only public metadata. A provider callable releases the
inference credential solely to the host relay. Management credentials are never
persisted. Key limits are provider backstops, not a proven exact in-flight cap.
"""
from __future__ import annotations
from contextlib import contextmanager
from decimal import Decimal
import hashlib
import json
import os
from pathlib import Path
import secrets
from urllib import request
from .config import _decimal

KEY_API_SOURCE = "https://openrouter.ai/docs/api/api-reference/api-keys/create-a-new-api-key"

class CredentialError(RuntimeError):
    pass

def _key(value):
    if not isinstance(value, str) or not value or any(ord(char) < 33 or ord(char) == 127 for char in value):
        raise CredentialError("Invalid host credential")
    return value

def _identity(proof_id):
    if not isinstance(proof_id, str) or not proof_id.strip() or len(proof_id) > 256:
        raise CredentialError("A stable run/proof identity is required")
    return proof_id

def _cap(value):
    cap = _decimal(value, "key limit", positive=True)
    if cap > 3:
        raise CredentialError("Per-proof provider limit cannot exceed USD 3")
    # The API accepts a JSON number, including sub-cent limits. Refuse any
    # value whose number representation would silently change the chosen cap.
    if Decimal(str(float(cap))) != cap:
        raise CredentialError("Provider key cap must round-trip exactly as a JSON number")
    return cap

class _NoRedirect(request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None

class KeyTransport:
    """One-shot HTTPS calls; exceptions contain no upstream response or secrets."""
    def __init__(self):
        self.opener = request.build_opener(_NoRedirect())

    def call(self, method, path, api_key, payload=None):
        if path != "/key" and path != "/keys" and not path.startswith("/keys/"):
            raise CredentialError("Invalid credential endpoint")
        data = None if payload is None else json.dumps(payload).encode()
        req = request.Request("https://openrouter.ai/api/v1" + path, data=data, method=method,
                              headers={"Authorization": "Bearer " + _key(api_key), "Content-Type": "application/json"})
        try:
            with self.opener.open(req, timeout=30) as response:
                raw = response.read(1_048_577)
                if len(raw) > 1_048_576:
                    raise ValueError()
                result = json.loads(raw, parse_float=Decimal)
                if not isinstance(result, dict):
                    raise ValueError()
                return result
        except Exception:
            raise CredentialError("Host credential API operation failed; inspect provider state before retrying creation") from None


class InferenceKeyFile:
    """One ordinary host key shared by independently metered proof relays.

    The caller checks agent-visible mounts before constructing this object.
    Verification is read-only authentication/metadata validation, not a claim
    about model access, funding, or any independently enforced proof budget.
    """
    def __init__(self, path, *, transport=None):
        self.path = Path(path).expanduser().resolve()
        self.transport = transport or KeyTransport()

    def credential(self):
        try:
            if self.path.stat().st_mode & 0o077:
                raise CredentialError("Inference key file permissions must be 0600")
            return _key(self.path.read_text(encoding="utf-8").strip())
        except CredentialError:
            raise
        except Exception:
            raise CredentialError("Host inference key file is unavailable") from None

    def verify(self):
        key = self.credential()
        result = self.transport.call("GET", "/key", key)
        data = result.get("data")
        try:
            if not isinstance(data, dict) or not data:
                raise ValueError()
            # Some documented /key responses omit these optional flags.
            for field in ("is_management_key", "is_provisioning_key", "disabled"):
                if field in data and type(data[field]) is not bool:
                    raise ValueError()
                if data.get(field) is True:
                    raise ValueError()
            _decimal(data.get("usage"), "provider key usage")
            for field in ("limit", "limit_remaining", "byok_usage"):
                if data.get(field) is not None:
                    _decimal(data[field], "provider " + field)
        except (ValueError, TypeError):
            raise CredentialError("Provider metadata does not identify an available ordinary inference key") from None
        # Aggregate usage is deliberately not returned as a proof charge.
        return {"key_sha256": hashlib.sha256(key.encode()).hexdigest(),
                "verification": "read_only_provider_metadata", "provider_budget_is_per_proof": False}

    def provider(self, fingerprint):
        """Check the run binding on every read, including the first dispatch."""
        def credential():
            key = self.credential()
            if hashlib.sha256(key.encode()).hexdigest() != fingerprint:
                raise CredentialError("Run inference key identity is immutable")
            return key
        return credential


class ProofKeyStore:
    """Private durable mapping from an immutable budget identity to one key.

    Pass forbidden_roots containing the project, runs and agent trees. The
    caller must keep this host file outside sandbox mount roots. A pending key
    creation survives interruption and prevents a second key/reset on resume.
    """
    def __init__(self, path, *, forbidden_roots=(), transport=None):
        self.path = Path(path).expanduser().resolve()
        for root in (Path(__file__).resolve().parents[2], *forbidden_roots):
            if self.path.is_relative_to(Path(root).resolve()):
                raise CredentialError("Credential store must be outside all project/run/agent roots")
        self.transport = transport or KeyTransport()

    @contextmanager
    def _locked(self):
        import fcntl
        self.path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        lock_path = self.path.with_name(self.path.name + ".lock")
        descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR, 0o600)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            if self.path.exists():
                if self.path.stat().st_mode & 0o077:
                    raise CredentialError("Credential store permissions must be 0600")
                data = json.loads(self.path.read_text(encoding="utf-8"))
                if data.get("schema_version") != 1 or not isinstance(data.get("proofs"), dict):
                    raise CredentialError("Malformed host credential store")
            else:
                data = {"schema_version": 1, "proofs": {}}
            yield data
        except CredentialError:
            raise
        except Exception:
            raise CredentialError("Host credential store operation failed") from None
        finally:
            os.close(descriptor)

    def _write(self, data):
        temporary = self.path.with_name("." + self.path.name + "." + secrets.token_hex(8))
        descriptor = os.open(temporary, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
        try:
            with os.fdopen(descriptor, "w", encoding="utf-8") as destination:
                json.dump(data, destination, sort_keys=True, indent=2)
                destination.write("\n")
                destination.flush()
                os.fsync(destination.fileno())
            temporary.replace(self.path)
            directory = os.open(self.path.parent, os.O_DIRECTORY)
            try:
                os.fsync(directory)
            finally:
                os.close(directory)
        finally:
            temporary.unlink(missing_ok=True)

    @staticmethod
    def _public(record):
        return {name: value for name, value in record.items() if name != "api_key"}

    @staticmethod
    def _verify_metadata(data, cap, *, fresh):
        if (not isinstance(data, dict) or data.get("is_management_key") is not False
                or data.get("disabled") is True or "limit_reset" not in data or data["limit_reset"] is not None
                or data.get("include_byok_in_limit") is not True
                or data.get("limit") is None or _decimal(data["limit"], "provider key limit") != cap):
            raise CredentialError("Proof key must have the exact no-reset cap, BYOK included, and inference access")
        usage = _decimal(data.get("usage"), "provider key usage")
        byok_usage = _decimal(data.get("byok_usage", "0"), "provider BYOK usage")
        if fresh and (usage != 0 or byok_usage != 0):
            raise CredentialError("A new proof identity requires an unused key")
        return usage

    def register(self, proof_id, api_key, *, limit_usd, verify=True):
        """Register a supplied per-proof key. Verification is a read-only GET."""
        proof_id, api_key, cap = _identity(proof_id), _key(api_key), _cap(limit_usd)
        fingerprint = hashlib.sha256(api_key.encode()).hexdigest()
        with self._locked() as store:
            existing = store["proofs"].get(proof_id)
            if existing:
                if existing.get("fingerprint") != fingerprint or Decimal(existing["limit_usd"]) != cap or existing.get("state") != "active":
                    raise CredentialError("Proof key identity and cap are immutable")
                return self._public(existing)
            if any(record.get("fingerprint") == fingerprint for record in store["proofs"].values()):
                raise CredentialError("One provider key cannot fund two proof identities")
            if not verify:
                raise CredentialError("Provided keys require read-only provider metadata verification")
            data = self.transport.call("GET", "/key", api_key).get("data")
            self._verify_metadata(data, cap, fresh=True)
            record = {"api_key": api_key, "fingerprint": fingerprint, "limit_usd": str(cap),
                      "ownership": "provided", "state": "active", "no_reset_verified": True,
                      "provider_key_hash": data.get("hash"), "source": KEY_API_SOURCE}
            store["proofs"][proof_id] = record
            self._write(store)
            return self._public(record)

    def provision(self, proof_id, management_key, *, limit_usd):
        """Explicit mutation: create once; uncertainty blocks automatic recreation."""
        proof_id, cap = _identity(proof_id), _cap(limit_usd)
        _key(management_key)
        with self._locked() as store:
            record = store["proofs"].get(proof_id)
            if record:
                if record.get("state") == "active" and Decimal(record["limit_usd"]) == cap:
                    return self._public(record)
                raise CredentialError("Existing proof key or uncertain creation requires host review; no replacement will be created")
            record = {"limit_usd": str(cap), "ownership": "managed", "state": "provisioning_unknown",
                      "name": "lean-proof-" + hashlib.sha256(proof_id.encode()).hexdigest()[:32], "source": KEY_API_SOURCE}
            store["proofs"][proof_id] = record
            self._write(store)
            # No reset, no expiration, no limit increase on resume. Decimal caps
            # are at most USD3; conversion is exact for supported half-dollar caps.
            result = self.transport.call("POST", "/keys", management_key,
                                         {"name": record["name"], "limit": float(cap), "limit_reset": None,
                                          "include_byok_in_limit": True})
            api_key = _key(result.get("key"))
            fingerprint = hashlib.sha256(api_key.encode()).hexdigest()
            if any(other.get("fingerprint") == fingerprint for identity, other in store["proofs"].items() if identity != proof_id):
                raise CredentialError("Provider returned an already assigned proof key")
            # Persist returned secret before further network operations, so a
            # failed verification never loses the only plaintext copy.
            record.update(api_key=api_key, fingerprint=fingerprint, provider_key_hash=result.get("data", {}).get("hash"), state="verification_pending")
            self._write(store)
            data = self.transport.call("GET", "/key", api_key).get("data")
            self._verify_metadata(data, cap, fresh=True)
            record.update(state="active", no_reset_verified=True)
            self._write(store)
            return self._public(record)

    def verify_pending(self, proof_id):
        """Retry only read-only verification of an already durably saved key."""
        with self._locked() as store:
            record = store["proofs"].get(_identity(proof_id))
            if not record or record.get("state") != "verification_pending" or not record.get("api_key"):
                raise CredentialError("No durably saved key awaits verification")
            data = self.transport.call("GET", "/key", record["api_key"]).get("data")
            self._verify_metadata(data, Decimal(record["limit_usd"]), fresh=True)
            record.update(state="active", no_reset_verified=True)
            self._write(store)
            return self._public(record)

    def metadata(self, proof_id):
        with self._locked() as store:
            record = store["proofs"].get(_identity(proof_id))
            if not record:
                raise CredentialError("No key is bound to this proof identity")
            return self._public(record)

    def provider(self, proof_id):
        proof_id = _identity(proof_id)
        def credential():
            with self._locked() as store:
                record = store["proofs"].get(proof_id)
                if not record or record.get("state") != "active":
                    raise CredentialError("Proof inference key is unavailable")
                return _key(record["api_key"])
        return credential

    def inspect(self, proof_id):
        """Read current per-key metadata without returning any key material."""
        key = self.provider(proof_id)()
        data = self.transport.call("GET", "/key", key).get("data")
        if not isinstance(data, dict):
            raise CredentialError("Invalid provider key metadata")
        return {name: str(data[name]) if isinstance(data.get(name), Decimal) else data.get(name)
                for name in ("limit", "limit_remaining", "limit_reset", "usage", "byok_usage", "include_byok_in_limit", "is_management_key", "disabled")}

    def disable(self, proof_id, management_key):
        """Explicit mutation: disable a managed key, retaining immutable receipts."""
        with self._locked() as store:
            record = store["proofs"].get(_identity(proof_id))
            if not record or record.get("ownership") != "managed" or not record.get("provider_key_hash"):
                raise CredentialError("A managed key hash is required for disable")
            key_hash = record["provider_key_hash"]
            if not isinstance(key_hash, str) or not key_hash.isalnum():
                raise CredentialError("Invalid provider key hash")
            record["state"] = "disable_pending"
            self._write(store)
            self.transport.call("PATCH", "/keys/" + key_hash, management_key, {"disabled": True})
            record["state"] = "disabled"
            self._write(store)
            return self._public(record)

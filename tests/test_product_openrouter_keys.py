"""Host key lifecycle tests use a synthetic in-memory API only."""
from decimal import Decimal
import json
import pytest
from harness.openrouter import ProofKeyStore, CredentialError

KEY = "synthetic-inference-credential"
MANAGEMENT = "synthetic-management-credential"

class KeyAPI:
    def __init__(self, *, usage="0", reset=None, failure=None, limit="1.5"):
        self.calls = []
        self.usage = usage
        self.reset = reset
        self.failure = failure
        self.limit = limit
    def call(self, method, path, api_key, payload=None):
        self.calls.append((method, path, payload))
        if self.failure:
            raise CredentialError("synthetic unavailable")
        data = {"hash": "a123", "limit": float(self.limit), "limit_reset": self.reset, "usage": self.usage,
                "include_byok_in_limit": True, "is_management_key": False, "disabled": False}
        return {"data": data, **({"key": KEY} if method == "POST" else {})}

def test_provision_once_no_reset_limit_and_secret_only_private_store(tmp_path):
    api = KeyAPI()
    path = tmp_path / "host" / "keys.json"
    store = ProofKeyStore(path, forbidden_roots=(tmp_path / "run",), transport=api)
    public = store.provision("run/proof", MANAGEMENT, limit_usd="1.5")
    assert public["state"] == "active"
    assert KEY not in json.dumps(public) and MANAGEMENT not in path.read_text()
    assert store.provider("run/proof")() == KEY
    assert path.stat().st_mode & 0o777 == 0o600
    assert api.calls[0] == ("POST", "/keys", {"name": public["name"], "limit": 1.5, "limit_reset": None, "include_byok_in_limit": True})
    assert api.calls[1] == ("GET", "/key", None)
    assert ProofKeyStore(path, transport=api).provision("run/proof", MANAGEMENT, limit_usd="1.5") == public
    assert len(api.calls) == 2
    with pytest.raises(CredentialError):
        store.provision("run/proof", MANAGEMENT, limit_usd="3")

def test_uncertain_creation_never_creates_replacement_on_resume(tmp_path):
    api = KeyAPI(failure=True)
    path = tmp_path / "private.json"
    store = ProofKeyStore(path, transport=api)
    with pytest.raises(CredentialError):
        store.provision("run/proof", MANAGEMENT, limit_usd="1.5")
    api.failure = None
    with pytest.raises(CredentialError, match="no replacement"):
        ProofKeyStore(path, transport=api).provision("run/proof", MANAGEMENT, limit_usd="1.5")
    assert len(api.calls) == 1
    assert store.metadata("run/proof")["state"] == "provisioning_unknown"


def test_subcent_cap_round_trips_without_a_silent_increase(tmp_path):
    api = KeyAPI(limit="0.001")
    store = ProofKeyStore(tmp_path / "keys.json", transport=api)
    result = store.provision("tiny/proof", MANAGEMENT, limit_usd="0.001")
    assert result["state"] == "active" and result["limit_usd"] == "0.001"
    assert api.calls[0][2]["limit"] == 0.001
    with pytest.raises(CredentialError, match="round-trip"):
        store.provision("unrepresentable/proof", MANAGEMENT, limit_usd="1.00000000000000001")
    assert len(api.calls) == 2

def test_provided_unused_key_read_only_verification_no_management_required(tmp_path):
    api = KeyAPI()
    store = ProofKeyStore(tmp_path / "keys.json", transport=api)
    result = store.register("run/proof", KEY, limit_usd="1.5")
    assert result["ownership"] == "provided"
    assert api.calls == [("GET", "/key", None)]
    assert store.register("run/proof", KEY, limit_usd="1.5") == result
    with pytest.raises(CredentialError, match="two proof"):
        store.register("run/other", KEY, limit_usd="1.5")
    with pytest.raises(CredentialError, match="immutable"):
        store.register("run/proof", "another-synthetic-key", limit_usd="1.5")

@pytest.mark.parametrize("usage,reset", [("0.1", None), ("0", "daily")])
def test_prior_use_and_reset_limits_rejected(tmp_path, usage, reset):
    store = ProofKeyStore(tmp_path / "keys.json", transport=KeyAPI(usage=usage, reset=reset))
    with pytest.raises(CredentialError):
        store.register("run/proof", KEY, limit_usd="1.5")
    assert not store.path.exists()

def test_store_cannot_enter_run_tree(tmp_path):
    with pytest.raises(CredentialError, match="outside"):
        ProofKeyStore(tmp_path / "run" / "keys.json", forbidden_roots=(tmp_path / "run",))

def test_disable_keeps_identity_and_prevents_credential_release(tmp_path):
    api = KeyAPI()
    store = ProofKeyStore(tmp_path / "keys.json", transport=api)
    store.provision("run/proof", MANAGEMENT, limit_usd="1.5")
    assert store.disable("run/proof", MANAGEMENT)["state"] == "disabled"
    assert api.calls[-1] == ("PATCH", "/keys/a123", {"disabled": True})
    with pytest.raises(CredentialError):
        store.provider("run/proof")()
    with pytest.raises(CredentialError):
        store.provision("run/proof", MANAGEMENT, limit_usd="1.5")

def test_returned_key_survives_verification_interruption_without_new_post(tmp_path):
    class InterruptedAPI(KeyAPI):
        def call(self, method, path, api_key, payload=None):
            result = super().call(method, path, api_key, payload)
            if method == "GET" and len(self.calls) == 2:
                raise CredentialError("verification interrupted")
            return result
    api = InterruptedAPI()
    store = ProofKeyStore(tmp_path / "keys.json", transport=api)
    with pytest.raises(CredentialError):
        store.provision("run/proof", MANAGEMENT, limit_usd="1.5")
    assert store.metadata("run/proof")["state"] == "verification_pending"
    assert store.verify_pending("run/proof")["state"] == "active"
    assert [method for method, path, payload in api.calls].count("POST") == 1


def test_inspect_includes_byok_usage_without_credential_material(tmp_path):
    class ByokAPI(KeyAPI):
        def call(self, *args, **kwargs):
            result = super().call(*args, **kwargs)
            result["data"]["byok_usage"] = Decimal("0.000096") if len(self.calls) > 1 else Decimal("0")
            return result
    api = ByokAPI()
    store = ProofKeyStore(tmp_path / "host.json", transport=api)
    store.register("run/proof", KEY, limit_usd="1.5")
    result = store.inspect("run/proof")
    assert result["byok_usage"] == "0.000096"
    assert result["usage"] == "0"
    assert KEY not in json.dumps(result)


def test_ordinary_shared_key_accepts_used_unlimited_or_resetting_account_metadata(tmp_path):
    from harness.openrouter import InferenceKeyFile
    path = tmp_path / "host.key"
    path.write_text(KEY); path.chmod(0o600)
    class API:
        def __init__(self):
            self.calls = []
        def call(self, method, route, api_key):
            self.calls.append((method, route))
            assert api_key == KEY
            return {"data": {"limit": None, "limit_reset": "daily", "usage": "123.45",
                "byok_usage": "67.89", "include_byok_in_limit": False}}
    api = API()
    source = InferenceKeyFile(path, transport=api)
    metadata = source.verify()
    assert api.calls == [("GET", "/key")]
    assert metadata["provider_budget_is_per_proof"] is False
    assert not {"usage", "byok_usage", "limit"} & metadata.keys()
    assert KEY not in json.dumps(metadata) and source.credential() == KEY


@pytest.mark.parametrize("field,value", [("is_management_key", True), ("is_provisioning_key", True),
    ("disabled", True), ("is_management_key", "false"), ("usage", "NaN"), ("usage", None)])
def test_ordinary_key_rejects_unavailable_or_invalid_metadata(tmp_path, field, value):
    from harness.openrouter import InferenceKeyFile
    path = tmp_path / "host.key"; path.write_text(KEY); path.chmod(0o600)
    class API:
        def call(self, *args):
            return {"data": {"usage": "0", field: value}}
    with pytest.raises(CredentialError):
        InferenceKeyFile(path, transport=API()).verify()


def test_ordinary_key_requires_private_permissions_before_provider_access(tmp_path):
    from harness.openrouter import InferenceKeyFile
    path = tmp_path / "host.key"; path.write_text(KEY); path.chmod(0o644)
    class API:
        def call(self, *args):
            pytest.fail("exposed key must never be verified")
    with pytest.raises(CredentialError, match="0600"):
        InferenceKeyFile(path, transport=API()).verify()


def test_shared_provider_rechecks_run_fingerprint_before_first_inference(tmp_path):
    import hashlib
    from harness.openrouter import InferenceKeyFile
    path = tmp_path / "host.key"; path.write_text(KEY); path.chmod(0o600)
    source = InferenceKeyFile(path)
    provider = source.provider(hashlib.sha256(KEY.encode()).hexdigest())
    path.write_text("different-synthetic-credential")
    with pytest.raises(CredentialError, match="immutable"):
        provider()

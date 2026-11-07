"""Host-only OpenRouter provider boundary; frozen public profiles contain no secrets."""
from .config import OpenRouterSettings, load_openrouter_settings
from .ledger import OpenRouterLedger, LedgerError, BudgetExhausted, UnsettledRequest, read_openrouter_receipt
from .relay import OpenRouterRelay
from .keys import ProofKeyStore, InferenceKeyFile, CredentialError

# Keep ``python -m harness.openrouter.model`` free of import-before-execution
# warnings while retaining the public package-level profile helpers.
def __getattr__(name):
    if name in {"native_model_catalog", "prepare_model", "write_prepared_model", "ModelPreparationError"}:
        from . import model
        value = getattr(model, name)
        globals()[name] = value
        return value
    raise AttributeError(name)

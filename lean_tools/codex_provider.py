from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import json
import os
import sys
from pathlib import Path

DEFAULT_PROVIDER = "openai"
OPENROUTER_PROVIDER = "openrouter"
OPENROUTER_API_KEY_ENV = "OPENROUTER_API_KEY"
OPENROUTER_PRESET_SLUG_ENV = "LEAN_REFACTOR_OPENROUTER_PRESET_SLUG"
OPENROUTER_PRESET_VERSION_ENV = "LEAN_REFACTOR_OPENROUTER_PRESET_VERSION"
OPENROUTER_SPEND_OWNER_ENV = "LEAN_REFACTOR_OPENROUTER_SPEND_OWNER"
PROVIDERS = (DEFAULT_PROVIDER, OPENROUTER_PROVIDER)
NONINTERACTIVE_APPROVAL_POLICY = "never"
NONINTERACTIVE_SANDBOX = "workspace-write"
WINDOWS_SANDBOX_IMPLEMENTATION = "elevated"
WINDOWS_GIT_SAFE_DIRECTORY = "*"


class ProviderError(ValueError):
    pass


def require_environment(provider: str) -> None:
    if provider not in PROVIDERS:
        raise ProviderError(f"unsupported Codex model provider: {provider}")
    if provider == OPENROUTER_PROVIDER and not os.environ.get(
        OPENROUTER_API_KEY_ENV, ""
    ).strip():
        raise ProviderError(
            f"{OPENROUTER_API_KEY_ENV} is not visible to this process; set it as a "
            "user environment variable and restart Codex before an OpenRouter run"
        )


def _toml_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def _toml_array(values: list[str]) -> str:
    return "[" + ",".join(_toml_string(value) for value in values) + "]"


def codex_config_args(provider: str) -> list[str]:
    if provider == DEFAULT_PROVIDER:
        return []
    if provider != OPENROUTER_PROVIDER:
        raise ProviderError(f"unsupported Codex model provider: {provider}")

    auth_command = sys.executable
    auth_args = [
        "-c",
        'import os; print(os.environ["OPENROUTER_API_KEY"])',
    ]

    values = (
        ("model_provider", _toml_string(OPENROUTER_PROVIDER)),
        ("model_providers.openrouter.name", _toml_string("openrouter")),
        (
            "model_providers.openrouter.base_url",
            _toml_string("https://openrouter.ai/api/v1"),
        ),
        ("model_providers.openrouter.wire_api", _toml_string("responses")),
        (
            "model_providers.openrouter.auth.command",
            _toml_string(auth_command),
        ),
        ("model_providers.openrouter.auth.args", _toml_array(auth_args)),
    )
    return [argument for key, value in values for argument in ("-c", f"{key}={value}")]


def windows_sandbox_environment() -> dict[str, str]:
    if os.name != "nt":
        return {}
    elan_home = os.environ.get("ELAN_HOME") or str(Path.home() / ".elan")
    return {
        "ELAN_HOME": elan_home,
        # Cached Lean dependencies are intentionally prepared by the interactive
        # Windows user, while elevated agents run as CodexSandboxOffline. Tell Git
        # that these read-mostly experiment repositories are trusted for this child
        # process only; do not mutate the user's global Git configuration.
        "GIT_CONFIG_COUNT": "1",
        "GIT_CONFIG_KEY_0": "safe.directory",
        "GIT_CONFIG_VALUE_0": WINDOWS_GIT_SAFE_DIRECTORY,
    }


def codex_noninteractive_args(
    writable_roots: list[str] | None = None,
) -> list[str]:
    """Disable approval prompts while retaining narrowly scoped write access.

    Agent commands ignore the user's config for experiment isolation, so Windows must
    select its provisioned sandbox backend explicitly. Otherwise Codex can reject every
    process launch even though ``workspace-write`` itself was requested.
    """
    roots = writable_roots or []
    windows_environment = windows_sandbox_environment()
    return [
        "-c",
        f'approval_policy="{NONINTERACTIVE_APPROVAL_POLICY}"',
        *(
            ["-c", f'windows.sandbox="{WINDOWS_SANDBOX_IMPLEMENTATION}"']
            if os.name == "nt"
            else []
        ),
        *(
            argument
            for key, value in windows_environment.items()
            for argument in (
                "-c",
                f"shell_environment_policy.set.{key}={_toml_string(value)}",
            )
        ),
        "--sandbox",
        NONINTERACTIVE_SANDBOX,
        *(argument for root in roots for argument in ("--add-dir", root)),
    ]


def billing_mode(provider: str) -> str:
    if provider == DEFAULT_PROVIDER:
        return "chatgpt_subscription_development"
    if provider == OPENROUTER_PROVIDER:
        return "openrouter_api"
    raise ProviderError(f"unsupported Codex model provider: {provider}")

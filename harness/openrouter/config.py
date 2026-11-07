"""Public, immutable OpenRouter request and spending settings.

Prices and routing come from a prepared catalog snapshot. Credentials are
host-only state and never belong in an experiment snapshot.
"""
from __future__ import annotations

from dataclasses import dataclass, fields
from decimal import Decimal, InvalidOperation
import json
from pathlib import Path
from typing import Mapping


CODEX_REASONING_EFFORTS = ("none", "minimal", "low", "medium", "high", "xhigh", "max", "ultra")


def _decimal(value, name: str, *, positive: bool = False) -> Decimal:
    try:
        result = Decimal(str(value))
    except (InvalidOperation, ValueError, TypeError) as error:
        raise ValueError(f"OpenRouter {name} must be finite and {'positive' if positive else 'nonnegative'}") from error
    if isinstance(value, bool) or not result.is_finite() or (result <= 0 if positive else result < 0):
        raise ValueError(f"OpenRouter {name} must be finite and {'positive' if positive else 'nonnegative'}")
    return result


def _decimal_text(value: Decimal) -> str:
    text = format(value, "f")
    return text.rstrip("0").rstrip(".") if "." in text else text


@dataclass(frozen=True)
class OpenRouterSettings:
    """Frozen prices and a single provider for one independently capped proof."""

    model_id: str
    provider: str
    input_price_per_million: Decimal
    output_price_per_million: Decimal
    context_length: int
    max_output_tokens: int
    supports_parallel_tool_calls: bool = False
    budget_usd: Decimal = Decimal("3")
    catalog_retrieved_at: str | None = None
    catalog_source: str | None = None
    supported_reasoning_efforts: tuple[str, ...] | None = None
    default_reasoning_effort: str | None = None
    model_display_name: str | None = None
    automatic_prompt_cache: bool = False

    def __post_init__(self) -> None:
        for name in ("model_id", "provider"):
            value = getattr(self, name)
            if (not isinstance(value, str) or not value.strip() or value != value.strip()
                    or any(character.isspace() for character in value)):
                raise ValueError(f"OpenRouter {name} must be a nonempty identifier without whitespace")
        if "/" not in self.model_id:
            raise ValueError("OpenRouter model_id must be an exact catalog model slug")
        for name in ("input_price_per_million", "output_price_per_million", "budget_usd"):
            object.__setattr__(self, name, _decimal(getattr(self, name), name, positive=name == "budget_usd"))
        for name in ("context_length", "max_output_tokens"):
            if type(getattr(self, name)) is not int or getattr(self, name) <= 0:
                raise ValueError(f"OpenRouter {name} must be a positive integer")
        if self.max_output_tokens > self.context_length:
            raise ValueError("OpenRouter max_output_tokens must not exceed context_length")
        if self.budget_usd > Decimal("3"):
            raise ValueError("OpenRouter per-proof cap must not exceed USD 3")
        if type(self.supports_parallel_tool_calls) is not bool:
            raise ValueError("supports_parallel_tool_calls must be boolean")
        if type(self.automatic_prompt_cache) is not bool:
            raise ValueError("automatic_prompt_cache must be boolean")
        if self.automatic_prompt_cache and not self.model_id.startswith("anthropic/"):
            raise ValueError("automatic_prompt_cache requires an Anthropic model")
        for name in ("catalog_retrieved_at", "catalog_source", "model_display_name"):
            value = getattr(self, name)
            if value is not None and (not isinstance(value, str) or not value.strip()):
                raise ValueError(f"OpenRouter {name} must be a nonempty string or None")
        efforts = self.supported_reasoning_efforts
        if efforts is not None:
            if (not isinstance(efforts, (tuple, list)) or not efforts
                    or any(not isinstance(effort, str) or effort not in CODEX_REASONING_EFFORTS for effort in efforts)
                    or len(set(efforts)) != len(efforts)):
                raise ValueError("OpenRouter supported_reasoning_efforts must be distinct supported Codex efforts")
            object.__setattr__(self, "supported_reasoning_efforts", tuple(efforts))
        if self.default_reasoning_effort is not None:
            if efforts is None or self.default_reasoning_effort not in efforts:
                raise ValueError("OpenRouter default_reasoning_effort must be a frozen supported effort")

    def to_dict(self) -> dict:
        result = {item.name: getattr(self, item.name) for item in fields(self)}
        for name in ("input_price_per_million", "output_price_per_million", "budget_usd"):
            result[name] = _decimal_text(getattr(self, name))
        if self.supported_reasoning_efforts is not None:
            result["supported_reasoning_efforts"] = list(self.supported_reasoning_efforts)
        if not self.automatic_prompt_cache:
            result.pop("automatic_prompt_cache")
        for name in ("catalog_retrieved_at", "catalog_source", "supported_reasoning_efforts",
                     "default_reasoning_effort", "model_display_name"):
            if result[name] is None:
                result.pop(name)
        return result

    @classmethod
    def from_dict(cls, value: Mapping) -> OpenRouterSettings:
        if not isinstance(value, Mapping):
            raise ValueError("OpenRouter settings must be a mapping")
        names = {item.name for item in fields(cls)}
        required = {"model_id", "provider", "input_price_per_million", "output_price_per_million", "context_length", "max_output_tokens"}
        if not required <= set(value) <= names:
            raise ValueError("OpenRouter settings require explicit catalog prices, model, provider and context length and no unsupported fields")
        return cls(**dict(value))


    from_mapping = from_dict

def load_openrouter_settings(path: Path | str | Mapping) -> OpenRouterSettings:
    """Read prepared public settings without network access or credentials."""
    if isinstance(path, Mapping):
        return OpenRouterSettings.from_dict(path)
    return OpenRouterSettings.from_dict(json.loads(Path(path).read_text(encoding="utf-8-sig")))

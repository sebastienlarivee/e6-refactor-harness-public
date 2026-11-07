"""Render the sole production CONTROL prompt bundle.

The editable approval workspace and native reference messages are never runtime
inputs. A prepared run pins every selected bundled Markdown/JSON file.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shlex
import sys

from .experiment import EFFICIENT_CONTROL_PROMPT

TEMPLATES = ("agent-instructions.md", "start-prompt.md", "initial-briefing.md",
             "proof-guide.md", "commands.md")
FILES = (*TEMPLATES, "pass-variants.json", "dynamic-sections.json")
PASS_FIELDS = {"pass_opening", "starting_instructions", "incumbent_briefing",
               "source_visibility_notice", "incumbent_metrics_line"}
DYNAMIC_FIELDS = {"compatibility_root_argument_per_version",
                  "compatibility_oracle_fallback_prefix",
                  "compatibility_oracle_fallback_line_per_version",
                  "source_map_without_target_filename",
                  "source_visibility_notice_without_positive_start_line"}
FEEDBACK_DYNAMIC_FIELDS = DYNAMIC_FIELDS | {"source_search_root_line"}
PLACEHOLDER = re.compile(r"\{\{([^{}]*)\}\}")


def source_paths(variant: str) -> list[Path]:
    if variant != EFFICIENT_CONTROL_PROMPT:
        raise ValueError("Unsupported prompt_variant; historical prompts must use their original frozen release")
    from .config import REPO_ROOT
    bundle = REPO_ROOT / "prompts" / "runtime" / variant
    return [bundle / name for name in FILES]


def snapshot(variant: str) -> dict:
    # Bundle filenames are checkout-independent. The run's outer source_hashes
    # separately pins absolute source locations. A continuation may relocate
    # byte-identical prompt data, but cannot silently approve changed wording.
    # Preserve the current bundle identity, including its historical provenance.
    provenance = {"base_prompt_variant": "control-feedback-v2", "base_commit": "ebbb566",
                  "update_reason": "2026-10-27 direct scoring and selective immutable candidate batches with compact receipt recovery"}
    return {"variant": variant, **provenance,
            "source_hashes": {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                              for path in source_paths(variant)}}


def verify_snapshot(config: dict) -> None:
    from .experiment import experiment_spec
    variant = experiment_spec(config).prompt_variant
    if config.get("prompt_bundle") != snapshot(variant):
        raise ValueError("Frozen approved prompt bundle changed or is missing")


def _read(variant: str) -> tuple[dict[str, str], dict, dict[str, str]]:
    paths = {path.name: path for path in source_paths(variant)}
    templates = {name: paths[name].read_text(encoding="utf-8") for name in TEMPLATES}
    variants = json.loads(paths["pass-variants.json"].read_text(encoding="utf-8"))
    dynamic = json.loads(paths["dynamic-sections.json"].read_text(encoding="utf-8"))
    required_variants = {"first-pass", "continuation"}
    allowed_variants = required_variants | {"reference-rebuild", "reference-rebuild-continuation"}
    if (not isinstance(variants, dict)
            or not required_variants <= set(variants) <= allowed_variants):
        raise ValueError("Invalid approved prompt pass variants")
    for fields in variants.values():
        _validate_fields(fields, PASS_FIELDS, "pass variant")
    _validate_fields(dynamic, FEEDBACK_DYNAMIC_FIELDS, "dynamic sections")
    return templates, variants, dynamic


def _validate_fields(value: dict, names: set[str], label: str) -> None:
    if (not isinstance(value, dict) or set(value) != names
            or any(not isinstance(item, str) for item in value.values())):
        raise ValueError(f"Invalid approved prompt {label}")


def _expand(text: str, fields: dict[str, str], stack: tuple[str, ...] = ()) -> str:
    def substitute(match: re.Match[str]) -> str:
        name = match.group(1)
        if name not in fields:
            raise ValueError(f"Unknown approved prompt placeholder: {name}")
        if name in stack:
            raise ValueError(f"Cyclic approved prompt placeholder: {' -> '.join((*stack, name))}")
        return _expand(fields[name], fields, (*stack, name))
    rendered = PLACEHOLDER.sub(substitute, text)
    if "{{" in rendered or "}}" in rendered:
        raise ValueError("Malformed approved prompt placeholder")
    return rendered


def render_guide(config: dict) -> str:
    from .experiment import experiment_spec
    templates, _, _ = _read(experiment_spec(config).prompt_variant)
    return _expand(templates["proof-guide.md"], {
        "original_tokens": str(config["original_tokens"]),
        "original_heartbeats": str(config["original_heartbeats"]),
        "total_version_count": str(1 + len(config["compatibility"])),
    })


def _efficient_score_fields(config: dict, incumbent: dict, *, statement_first: bool,
                            total_versions: int) -> dict[str, str]:
    """Explain frozen measurements and denominator arithmetic without search advice."""
    from lean_tools.scoring import OriginalDenominatorScorePolicy, score_breakdown

    policy = OriginalDenominatorScorePolicy(config["original_tokens"], config["original_heartbeats"],
                                            config.get("scoring_policy", "legacy-v1"))
    fields = {
        "original_control_measurement_line": "",
        "incumbent_measurements": "",
        "score_sensitivity": (
            "Approximate combined-score changes with other metrics fixed, before component and final rounding: "
            f"one fewer proof token = +{100 / (3 * policy.original_tokens):.8g} points "
            "(`100 / (3*T0)`); "
            f"100 fewer exact primary heartbeats = +{10000 / (3 * policy.original_heartbeats):.8g} points "
            "(`10000 / (3*H0)`); "
            f"one supplied environment changing from fail to pass = +{100 / (3 * total_versions):.8g} points "
            f"(`100 / (3*N)`, `N = {total_versions}`)."
        ),
    }
    if statement_first:
        # The denominators are already public in this view. Do not reveal the
        # hidden original's measurements, score, or current control observation.
        return fields
    breakdown = score_breakdown(policy, tokens=incumbent["tokens"], heartbeats=incumbent["heartbeats"],
                                compatibility_pct=incumbent["compatibility_pct"])
    if breakdown["score"] != incumbent["score"]:
        raise ValueError("Verified incumbent score does not match its measurements")
    points = breakdown["score_points"]
    rows = ["| Verified metric | Measured value | Combined-score contribution |",
            "| --- | ---: | ---: |",
            f"| Proof tokens | {incumbent['tokens']} | {points['length']:.4f} points |",
            f"| Exact primary heartbeats | {incumbent['heartbeats']} | {points['heartbeats']:.4f} points |",
            f"| Compatibility | {incumbent['compatibility_pct']:g}% | {points['compatibility']:.4f} points |"]
    if breakdown["rounding_adjustment"]:
        rows.append(f"| Rounding adjustment | | {breakdown['rounding_adjustment']:+.4f} points |")
    rows.append(f"| Combined score | | {breakdown['score']:.4f}/100 |")
    control_heartbeats = config.get("observed_original_baseline", {}).get("heartbeats",
        config.get("original_measurement_heartbeats", config["original_heartbeats"]))
    fields.update(
        incumbent_measurements="\n".join(rows),
        original_control_measurement_line=(
            f" Current original-control measurement: {control_heartbeats} exact primary heartbeats; "
            "it does not replace `H0`."),
    )
    return fields


def write_capsule(capsule: Path, config: dict, incumbent: dict, *, statement_first: bool,
                  reference_rebuild: bool = False) -> None:
    """Expand all nested fields using this capsule's actual task and measurements."""
    from lean_tools import arena_workflow as arena
    from .config import TOOLS_ROOT
    from .experiment import experiment_spec
    variant = experiment_spec(config).prompt_variant
    verify_snapshot(config)
    templates, variants, dynamic = _read(variant)
    if statement_first and reference_rebuild:
        raise ValueError("A reference rebuild cannot use the statement-only view")
    key = "reference-rebuild" if reference_rebuild else "first-pass" if statement_first else "continuation"
    if key not in variants:
        raise ValueError("Prompt bundle does not support the selected pass mode")
    fields = dict(variants[key])
    _, row = arena.load_task(capsule / "Task.json")
    primary = Path(config["primary"]).resolve()
    roots = [Path(value).resolve() for value in config["compatibility"]]
    relative = row.get("file_path")
    if relative:
        target = (primary / relative).resolve()
        if not target.is_relative_to(primary):
            raise ValueError("Approved prompt target source escapes the project")
        relative = str(target.relative_to(primary))
        directory = str(Path(relative).parent)
    else:
        # This entire line is conditional; absent task metadata must not produce
        # a fabricated filename or expose an unresolved host placeholder.
        source_line = ("- Target source: `{{primary_project}}/{{target_relative_path}}`. "
                       "Source directory: `{{primary_project}}/{{target_relative_directory}}`."
                       "{{source_visibility_notice}}")
        if source_line not in templates["initial-briefing.md"]:
            raise ValueError("Approved source-map template changed")
        templates["initial-briefing.md"] = templates["initial-briefing.md"].replace(
            source_line, "- " + dynamic["source_map_without_target_filename"])
        relative, directory = "", ""
    line = row.get("start_line")
    if not statement_first and (type(line) is not int or line <= 0):
        fields["source_visibility_notice"] = dynamic["source_visibility_notice_without_positive_start_line"]
    fields.update(
        task_id=str(row["name"]), primary_project=str(primary),
        capsule=str(capsule.resolve()), tools_root=str(TOOLS_ROOT.resolve()),
        python=str(Path(sys.executable).resolve()),
        target_relative_path=relative, target_relative_directory=directory,
        target_start_line=str(line) if type(line) is int and line > 0 else "",
        original_tokens=str(config["original_tokens"]),
        original_heartbeats=str(config["original_heartbeats"]),
        original_control_heartbeats=str(config.get("observed_original_baseline", {}).get("heartbeats",
            config.get("original_measurement_heartbeats", config["original_heartbeats"]))),
        incumbent_tokens=str(incumbent["tokens"]), incumbent_heartbeats=str(incumbent["heartbeats"]),
        incumbent_compatibility_pct=f"{incumbent['compatibility_pct']:g}",
        incumbent_score=f"{incumbent['score']:g}", incumbent_sha256=incumbent["sha256"],
        candidate_sha256=arena.sha256_file(capsule / "Candidate.lean"),
        compatibility_count=str(len(roots)), total_version_count=str(1 + len(roots)),
        initial_briefing=templates["initial-briefing.md"],
    )
    if reference_rebuild:
        reference = capsule / "Original.lean"
        if arena.sha256_file(reference) != incumbent["sha256"]:
            raise ValueError("Original reference does not match the verified fallback")
        fields.update(reference_path=str(reference.resolve()), reference_sha256=incumbent["sha256"])
    if not statement_first and not reference_rebuild and fields["candidate_sha256"] != incumbent["sha256"]:
        raise ValueError("Starting Candidate.lean does not match the verified incumbent")
    fields.update(_efficient_score_fields(config, incumbent, statement_first=statement_first,
                                         total_versions=1 + len(roots)))
    from lean_tools.regional_profiler import profiler_capability
    capability = profiler_capability(row, primary)
    fields["profiler_capability_summary"] = (
        f"Profiling is available for this capsule's {capability['source_form']} source form "
        "in `regions` and `wall_time` modes. `timeout_seconds` defaults to "
        f"{capability['default_timeout_seconds']} seconds (maximum 30) per Lean process: "
        "optional source validation and profiling each get that allowance. Setup is bounded separately "
        "by the same value, and admission shares a separate 10-second budget. At defaults the stage "
        "allowances total at most 100 seconds before cleanup/artifact finalization; cached validation "
        "skips its process. There are no automatic retries. "
        f"`top_n` must be 1 through {capability['max_top_n']}."
        if capability["available"] else
        "Profiling is unavailable for this capsule's legal prefix. Use ordinary quick checks "
        "and complete scoring; repeated profiling requests will not repair the missing capability.")
    search_roots = [("Project source", primary)]
    mathlib = primary / ".lake" / "packages" / "mathlib" / "Mathlib"
    if mathlib.is_dir():
        search_roots.append(("Mathlib source", mathlib))
    fields["source_search_roots"] = "\n".join(
        _expand(dynamic["source_search_root_line"],
                {**fields, "source_search_label": label, "source_search_root": str(root)})
        for label, root in search_roots)
    fields["source_search_root_arguments"] = " ".join(
        shlex.quote(str(root)) for _, root in search_roots)
    # Display paths remain ordinary paths. Command paths are separate shell
    # arguments, including when templates concatenate a quoted root and suffix.
    shell_fields = {**fields, **{name: shlex.quote(fields[name]) for name in
                                ("primary_project", "capsule", "tools_root", "python")}}
    arguments, fallbacks = [], []
    for root in roots:
        local = {**shell_fields, "compatibility_project": shlex.quote(str(root))}
        arguments.append(_expand(dynamic["compatibility_root_argument_per_version"], local))
        fallbacks.append(_expand(dynamic["compatibility_oracle_fallback_line_per_version"], local))
    fields["compatibility_root_arguments"] = "".join(arguments)
    fields["compatibility_oracle_fallback"] = (
        _expand(dynamic["compatibility_oracle_fallback_prefix"], fields) + "\n".join(fallbacks)
        if roots else "")
    shell_fields.update(compatibility_root_arguments=fields["compatibility_root_arguments"],
                        compatibility_oracle_fallback=fields["compatibility_oracle_fallback"])
    # Validate even unused dynamic fragments (zero alternate versions, or no
    # source filename), so misspelled nested placeholders fail before dispatch.
    for name, value in dynamic.items():
        _expand(value, {**shell_fields, "compatibility_project": "/unused-compatibility-project",
                        "source_search_label": "Project source",
                        "source_search_root": str(primary)}, (name,))
    for name, value in fields.items():
        _expand(value, fields, (name,))
    documents = {"AGENTS.md": _expand(templates["agent-instructions.md"], fields),
                 "prompt.md": _expand(templates["start-prompt.md"], fields),
                 "LEAN_PROOF_GUIDE.md": _expand(templates["proof-guide.md"], fields),
                 "COMMANDS.md": _expand(templates["commands.md"], shell_fields)}
    for name, text in documents.items():
        (capsule / name).write_text(text, encoding="utf-8")

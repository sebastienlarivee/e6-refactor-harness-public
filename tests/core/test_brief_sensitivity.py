"""Source-bound verified briefings and neutral denominator sensitivity arithmetic."""
from dataclasses import replace
from decimal import Decimal
import re

import pytest

from e6 import prompt_bundle, statement_first
from e6.experiment import DEFAULT_RUN_SPEC, EFFICIENT_CONTROL_PROMPT
from lean_tools import arena_workflow as arena
from lean_tools.scoring import OriginalDenominatorScorePolicy


def render_brief(root, *, mode="reference", pass_number=1, tokens=5, heartbeats=27,
                 compatibility_pct=100 / 3, original_tokens=37, original_heartbeats=91,
                 versions=3):
    root.mkdir()
    primary = root / "primary"
    primary.mkdir()
    row = {"name": "Brief.task", "signature": "theorem Brief.task : True",
           "header": "", "contexts": [], "file_path": "Target.lean", "start_line": 3,
           "src": "theorem Brief.task : True := by exact True.intro\n"}
    (primary / "Target.lean").write_text("\n\n" + row["src"])
    (primary / "lean-toolchain").write_text("leanprover/lean4:v4.29.1")
    (primary / "lake-manifest.json").write_text('{"packages":[]}')
    spec = replace(DEFAULT_RUN_SPEC, prompt_variant=EFFICIENT_CONTROL_PROMPT,
                   candidate_batches=True, response_policy="compact-v1",
                   first_pass_reference_rebuild=mode == "reference",
                   first_pass_reprove=mode == "statement")
    config = {**spec.proof_settings(), "primary": str(primary),
              "compatibility": [str(root / f"alternate-{i}") for i in range(versions - 1)],
              "original_tokens": original_tokens, "original_heartbeats": original_heartbeats,
              "original_measurement_heartbeats": 79,
              "observed_original_baseline": {"heartbeats": 83}}
    source = arena.render_candidate_scaffold(row)
    policy = OriginalDenominatorScorePolicy(original_tokens, original_heartbeats)
    incumbent = {"source": source, "sha256": arena.sha256_bytes(source.encode()),
                 "tokens": tokens, "heartbeats": heartbeats, "compatibility_pct": compatibility_pct,
                 "score": policy.score(tokens=tokens, heartbeats=heartbeats,
                                       compatibility_pct=compatibility_pct)}
    candidate_row = statement_first.statement_row(row) if mode in {"reference", "statement"} else row
    arena.write_json_atomic(root / "Task.json", {"schema_version": 1, "row": candidate_row})
    (root / "Candidate.lean").write_text(arena.render_candidate_scaffold(candidate_row))
    if mode == "reference":
        (root / "Original.lean").write_text(source)
    config["prompt_bundle"] = prompt_bundle.snapshot(EFFICIENT_CONTROL_PROMPT)
    prompt_bundle.write_capsule(root, config, incumbent, statement_first=mode == "statement",
                                reference_rebuild=mode == "reference")
    return config, incumbent, (root / "prompt.md").read_text()


def contribution_rows(text):
    return {label: Decimal(value) for label, value in re.findall(
        r"^\| ([^|]+?) \|[^|]*\| ([+-]?[\d.]+) points \|$", text, re.MULTILINE)}


@pytest.mark.parametrize("mode,pass_number", [
    ("reference", 1), ("refactor", 1), ("refactor", 2),
])
def test_verified_table_reconciles_and_binds_the_actual_starting_source(tmp_path, mode, pass_number):
    root = tmp_path / "capsule"
    _config, incumbent, text = render_brief(root, mode=mode, pass_number=pass_number)
    rows = contribution_rows(text)
    assert rows == {"Proof tokens": Decimal("28.8300"),
                    "Exact primary heartbeats": Decimal("23.4433"),
                    "Compatibility": Decimal("11.1111")}
    total = Decimal(re.search(r"\| Combined score \| \| ([\d.]+)/100 \|", text)[1])
    assert total == sum(rows.values()) == Decimal(str(incumbent["score"]))
    assert "| Proof tokens | 5 |" in text and "| Exact primary heartbeats | 27 |" in text
    assert "| Compatibility | 33.3333% |" in text
    assert text.count("| Verified metric |") == 1
    assert text.count("83 exact primary heartbeats") == 1
    assert "79 exact primary heartbeats" not in text
    assert "`T0 = 37`" in text and "`H0 = 91`" in text
    assert "it does not replace `H0`" in text
    assert incumbent["sha256"] in text
    candidate_hash = arena.sha256_file(root / "Candidate.lean")
    assert candidate_hash in text
    if mode == "reference":
        assert candidate_hash != incumbent["sha256"]
        assert "completed host checks belong to Original.lean; Candidate.lean starts unfinished" in text
        assert "original reference" in text
    else:
        assert candidate_hash == incumbent["sha256"]
        assert "starting incumbent in Candidate.lean (host checks complete)" in text
    assert "{{" not in text and "}}" not in text


@pytest.mark.parametrize("original_tokens,original_heartbeats,versions", [
    (37, 91, 3), (211, 104729, 5),
])
def test_sensitivity_uses_fixed_unequal_denominators_before_rounding(
        tmp_path, original_tokens, original_heartbeats, versions):
    _config, _incumbent, text = render_brief(tmp_path / "capsule", original_tokens=original_tokens,
        original_heartbeats=original_heartbeats, versions=versions)
    values = [float(value) for value in re.findall(r"= \+([\d.e+-]+) points", text)]

    def unrounded_score(tokens, heartbeats, passing):
        return (100 * (original_tokens - tokens) / original_tokens
                + 100 * (original_heartbeats - heartbeats) / original_heartbeats
                + 100 * passing / versions) / 3

    baseline = unrounded_score(9, 501, 1)
    expected = [unrounded_score(8, 501, 1) - baseline,
                unrounded_score(9, 401, 1) - baseline,
                unrounded_score(9, 501, 2) - baseline]
    assert values == pytest.approx(expected, rel=1e-7)
    assert "other metrics fixed, before component and final rounding" in text
    assert "Approximate combined-score changes" in text
    assert f"`N = {versions}`" in text


def test_rounding_adjustment_makes_displayed_contributions_sum_to_verified_total(tmp_path):
    _config, incumbent, text = render_brief(tmp_path / "capsule", tokens=0, heartbeats=0,
        compatibility_pct=100, original_tokens=100, original_heartbeats=100)
    rows = contribution_rows(text)
    assert rows["Rounding adjustment"] == Decimal("0.0001")
    assert sum(rows.values()) == Decimal("100.0000") == incumbent["score"]
    assert "| Combined score | | 100.0000/100 |" in text


def test_statement_view_exposes_only_denominator_arithmetic(tmp_path):
    root = tmp_path / "capsule"
    _config, incumbent, text = render_brief(root, mode="statement")
    assert "`T0 = 37`" in text and "`H0 = 91`" in text
    assert "Approximate combined-score changes" in text
    for name in ("prompt.md", "AGENTS.md", "COMMANDS.md", "LEAN_PROOF_GUIDE.md"):
        document = (root / name).read_text()
        assert incumbent["sha256"] not in document
        assert str(incumbent["score"]) not in document
        assert "| Verified metric |" not in document
        assert "original-control measurement" not in document
        assert "83 exact primary heartbeats" not in document
    # Arithmetic does not require access to a private incumbent at all.
    fields = prompt_bundle._efficient_score_fields(_config, {}, statement_first=True, total_versions=3)
    assert fields["incumbent_measurements"] == fields["original_control_measurement_line"] == ""


def test_brief_rejects_score_or_source_mismatch_instead_of_misattributing_metrics(tmp_path):
    root = tmp_path / "capsule"
    config, incumbent, _text = render_brief(root, mode="refactor")
    with pytest.raises(ValueError, match="score does not match"):
        prompt_bundle.write_capsule(root, config, {**incumbent, "score": incumbent["score"] + 1},
                                    statement_first=False)
    (root / "Candidate.lean").write_text("theorem Brief.task : True := by trivial\n")
    with pytest.raises(ValueError, match="does not match the verified incumbent"):
        prompt_bundle.write_capsule(root, config, incumbent, statement_first=False)

"""Released LeanPool rows use their pinned project prefix, including private scope.

The two rows are unmodified final-release records. Source files below are
synthetic so this regression needs no cached Lean environment or network.
"""
from pathlib import Path
import json

import pytest

from harness.benchmark import digest, load_benchmark, load_benchmark_rows
from harness.environments import EnvironmentMap, _selection
from lean_tools import lean_source
from lean_tools.task import normalize_arena_row
from lean_tools.workflow_errors import WorkflowError

FIXTURES = Path(__file__).parent / "fixtures"
ROWS = [json.loads(line) for line in (FIXTURES / "leanpool-final.jsonl").read_text().splitlines()]


def inputs(tmp_path, rows):
    benchmark, heartbeat = tmp_path / "final.jsonl", tmp_path / "references.jsonl"
    benchmark.write_text("".join(json.dumps(row) + "\n" for row in rows))
    # Synthetic references exercise ingestion only; they are never published baselines.
    heartbeat.write_text("".join(json.dumps({"name": row["name"], "heartbeat": 123}) + "\n" for row in rows))
    return benchmark, heartbeat


def test_released_rows_preserve_provenance_and_empty_supplied_header(tmp_path):
    input_path, heartbeat_path = inputs(tmp_path, ROWS)
    benchmark = load_benchmark(input_path, heartbeat_path)
    heartbeat_path.unlink()
    assert load_benchmark_rows(input_path) == benchmark.rows
    provenance = json.loads((FIXTURES / "leanpool-final-provenance.json").read_text())
    for raw, row, evidence in zip(ROWS, benchmark.rows, provenance["rows"], strict=True):
        assert digest(raw) == evidence["raw_row_sha256"]
        assert row == {**raw, "signature": raw["statement"].rstrip(), "contexts": []}
        assert lean_source.is_project_resident(row)
        assert lean_source.render_environment(row) == "\n\n"


@pytest.mark.parametrize("field,value", [("url", ""), ("url", None), ("file_path", "")])
def test_leanpool_requires_explicit_repository_and_source_path(tmp_path, field, value):
    row = {**ROWS[0], field: value}
    with pytest.raises(ValueError, match="explicit repository url and project file_path"):
        load_benchmark(*inputs(tmp_path, [row]))


def test_leanpool_selection_uses_repository_and_ordered_version_pins(tmp_path):
    row = normalize_arena_row(ROWS[0])
    snapshots = {}
    for index, item in enumerate(row["version_info"]):
        version, revision = next(iter(item.items()))
        snapshots[f"lp-{index}"] = {"repository": row["url"], "lean_version": version, "revision": revision}
        # Same version/revision at another repository must never win selection.
        snapshots[f"wrong-{index}"] = {**snapshots[f"lp-{index}"], "repository": "https://github.com/leanprover-community/mathlib4"}
    env = EnvironmentMap(tmp_path / "env.toml", tmp_path / "requirements.json", {},
        {"schema_version": 1, "snapshots": snapshots, "tasks": {}})
    label, selected = _selection(row, env, "arena-v1")
    assert label.startswith("proof-")
    assert selected == {"primary": "lp-0", "compatibility": ["lp-1"]}
    del snapshots["lp-0"]
    with pytest.raises(ValueError, match="Unsupported source snapshot"):
        _selection(row, env, "arena-v1")


@pytest.mark.parametrize("raw", ROWS, ids=lambda row: row["name"])
@pytest.mark.parametrize("module_header", [False, True])
def test_project_scaffold_uses_source_prefix_and_keeps_target_out_of_context(tmp_path, raw, module_header):
    row = normalize_arena_row(raw)
    declaration = lean_source.canonical_candidate_declaration(row)
    header = "module\n\npublic import Mathlib\n\n" if module_header else "import Mathlib\n\n"
    prefix = header + f"namespace {row['name'].rsplit('.', 1)[0]}\nvariable (M : Type)\ndef before := 7\n\n"
    source = tmp_path / row["file_path"]
    source.parent.mkdir(parents=True)
    source.write_text(prefix + row["src"] + "\n\nlemma later : True := by trivial\n")
    assert lean_source.quick_compile_harness(row, declaration, tmp_path) == prefix + declaration + "\n"
    exact_prefix = lean_source.exact_source_prefix(row, tmp_path)
    assert exact_prefix.text == prefix
    assert exact_prefix.source_path == source
    assert row["src"] not in exact_prefix.text
    measured = lean_source.project_compile_harness(row, declaration, tmp_path, exact=True)
    assert measured.endswith("lrh_measured_decl " + declaration + "\n")
    assert "lemma later" not in measured
    assert "def before := 7" in measured
    assert ("meta import LrhMeasurement" in measured) == module_header
    # Compatibility revisions may change whitespace; retain private visibility.
    source.write_text(prefix + row["src"].replace("theorem ", "theorem  ", 1))
    assert lean_source.quick_compile_harness(row, declaration, tmp_path) == prefix + declaration + "\n"
    if row["signature"].startswith("private "):
        source.write_text(prefix + row["src"].removeprefix("private "))
        with pytest.raises(WorkflowError, match="changed its scoped prefix"):
            lean_source.quick_compile_harness(row, declaration, tmp_path)
    # A changed compatibility statement must still fail the source identity check.
    source.write_text(prefix + row["src"].replace("theorem ", "theorem changed_", 1))
    with pytest.raises(WorkflowError, match="expected one structural source declaration"):
        lean_source.quick_compile_harness(row, declaration, tmp_path)


def test_missing_leanpool_source_cannot_fall_back_to_empty_supplied_header(tmp_path):
    row = normalize_arena_row(ROWS[0])
    with pytest.raises(WorkflowError, match="project source is missing"):
        lean_source.quick_compile_harness(row, lean_source.canonical_candidate_declaration(row), tmp_path)

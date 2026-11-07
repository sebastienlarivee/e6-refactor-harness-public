from pathlib import Path
import json
import pytest

from harness.benchmark import load_benchmark, digest
from harness.environments import load_environment_map, resolve_benchmark

ROOT = Path(__file__).resolve().parents[1]


def fixture_rows(tmp_path, rows=None, refs=None):
    originals = [json.loads(line) for line in (ROOT / "data/benchmark_data_warmup.jsonl").read_text().splitlines()]
    rows = rows if rows is not None else originals
    refs = refs if refs is not None else [json.loads(line) for line in (ROOT / "data/benchmark_heartbeats.jsonl").read_text().splitlines()]
    inp, hb = tmp_path / "contest.jsonl", tmp_path / "heartbeat.jsonl"
    inp.write_text("".join(json.dumps(row) + "\n" for row in rows))
    hb.write_text("".join(json.dumps(row) + "\n" for row in refs))
    return inp, hb


def test_shipped_rows_are_original_and_provenance_is_hashed():
    benchmark = load_benchmark(ROOT / "data/benchmark_data_warmup.jsonl", ROOT / "data/benchmark_heartbeats.jsonl")
    provenance = json.loads((ROOT / "data/benchmark-provenance.json").read_text())
    assert len(benchmark.rows) == 15
    for row, evidence in zip(benchmark.rows, provenance["rows"]):
        original = json.loads((ROOT / evidence["task_file"]).read_text())["row"]
        assert row == original
        assert digest(row) == evidence["row_sha256"]
    assert provenance["files"]["benchmark_data_warmup.jsonl"] == benchmark.input_sha256


def test_contest_ingestion_is_not_fixed_to_research_labels(tmp_path):
    original = json.loads((ROOT / "data/benchmark_data_warmup.jsonl").read_text().splitlines()[0])
    original.update(name="NewContest.declaration")
    inp, hb = fixture_rows(tmp_path, [original], [{"name": original["name"], "heartbeat": 123}])
    benchmark = load_benchmark(inp, hb)
    assert benchmark.rows[0]["name"] == "NewContest.declaration"
    assert len(benchmark.identity) == 64


@pytest.mark.parametrize("change,match", [
    (lambda rows: rows.append(dict(rows[0])), "Duplicate benchmark"),
    (lambda rows: rows[0].update(version_info=[{"v4.29.1": "main"}]), "full revisions"),
    (lambda rows: rows[0].update(file_path="../Escape.lean"), "within the snapshot"),
    (lambda rows: rows[0].update(proof_length=True), "proof_length"),
])
def test_invalid_original_input_rejected(tmp_path, change, match):
    rows = [json.loads((ROOT / "data/benchmark_data_warmup.jsonl").read_text().splitlines()[0])]
    change(rows)
    inp, hb = fixture_rows(tmp_path, rows)
    with pytest.raises(ValueError, match=match):
        load_benchmark(inp, hb)


def test_published_heartbeats_optional_partial_and_unique(tmp_path):
    inp, hb = fixture_rows(tmp_path, refs=[{"name": "wrong", "heartbeat": 12}])
    partial = load_benchmark(inp, hb)
    assert partial.heartbeats == {"wrong": 12}
    absent = load_benchmark(inp)
    assert absent.heartbeat_path is None and absent.heartbeats == {}
    assert absent.to_dict()["heartbeat_path"] is None
    hb.write_text("")
    assert load_benchmark(inp, hb).heartbeats == {}
    inp, hb = fixture_rows(tmp_path, refs=[{"name": "x", "heartbeat": 12}] * 2)
    with pytest.raises(ValueError, match="Duplicate heartbeat"):
        load_benchmark(inp, hb)


def test_pinned_putnam_arena_primaries_and_legacy_are_preserved():
    requirements = json.loads((ROOT / "data/environment-requirements.json").read_text())
    snapshots = requirements["snapshots"]
    expected = {"putnam_1964_a4": "v4.27.0", "putnam_1964_b2": "v4.26.0", "putnam_1995_a3": "v4.27.0"}
    for name, version in expected.items():
        row = requirements["tasks"][name]
        assert snapshots[row["arena-v1"]["primary"]]["lean_version"] == version
        assert snapshots[row["legacy-v1"]["primary"]]["lean_version"] == "v4.25.0"

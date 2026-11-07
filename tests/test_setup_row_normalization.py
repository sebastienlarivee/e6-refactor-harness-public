"""Public source manifests carry statement fields, not internal signature aliases."""
import json

from scripts.setup_environments import import_targets, rows_for_snapshot


def test_statement_only_manifest_rows_normalize_without_mutating_input(tmp_path):
    source = "theorem example : True := by trivial"
    row = {"name": "example", "statement": "theorem example : True", "src": source,
           "file_path": "Example.lean", "start_line": 3, "end_line": 3,
           "url": "https://github.com/example/project",
           "version_info": [{"v4.29.1": "a" * 40}]}
    manifest = {"rows": [row], "requirements": {"snapshots": {"fixture": {
        "repository": row["url"], "lean_version": "v4.29.1", "revision": "a" * 40}}}}
    normalized = rows_for_snapshot(manifest, "fixture")
    assert normalized[0]["signature"] == row["statement"]
    assert normalized[0]["contexts"] == []
    assert "signature" not in row and "contexts" not in row
    (tmp_path / "lake-manifest.json").write_text(json.dumps({"packages": []}))
    (tmp_path / "Dependency.lean").write_text("import Init\n")
    (tmp_path / "Example.lean").write_text("import Dependency\n\n" + source + "\n")
    assert import_targets(tmp_path, [row]) == [(None, "Dependency")]
    assert import_targets(tmp_path, normalized) == [(None, "Dependency")]

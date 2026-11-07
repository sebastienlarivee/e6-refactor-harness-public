from __future__ import annotations
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from pathlib import Path
import pytest

from lean_tools import arena_workflow as arena
from lean_tools import capsule as capsule_tools
SCRIPT = Path(arena.__file__)
resource_gate = arena.resource_gate

def sample_row() -> dict[str, object]:
    return {
        "name": "demo",
        "header": "import Mathlib\n\n",
        "contexts": [
            {
                "name": "helper",
                "kind": "def",
                "signature": "def helper : Prop",
                "src": "def helper : Prop := True",
            }
        ],
        "signature": "theorem demo : helper",
        "src": "theorem demo : helper := by trivial",
        "proof_length": 5,
    }

def write_sample_task_and_candidate(tmp_path: Path) -> tuple[Path, Path]:
    row = sample_row()
    task = tmp_path / "Task.json"
    task.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "reference": {"heartbeat": 1000},
                "local_baselines": [],
                "row": row,
            }
        ),
        encoding="utf-8",
    )
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text(
        arena.render_environment(row)
        + arena.TARGET_BEGIN
        + "theorem demo : helper := by\n  exact True.intro\n"
        + arena.TARGET_END,
        encoding="utf-8",
    )
    return task, candidate


def test_lean_code_mask_preserves_offsets_and_ignores_nested_comments() -> None:
    source = (
        "theorem demo : True := by\n"
        "  -- sorry in a line comment\n"
        '  have s := "axiom in a string"\n'
        "  /- outer sorry /- nested axiom -/ done -/\n"
        "  trivial\n"
    )
    masked = arena.lean_code_mask(source)
    assert len(masked) == len(source)
    assert masked.count("\n") == source.count("\n")
    assert "sorry" not in masked
    assert "axiom" not in masked
    assert "theorem demo" in masked
    assert "trivial" in masked

def test_extract_candidate_requires_exact_environment_and_signature() -> None:
    row = sample_row()
    candidate = (
        arena.render_environment(row)
        + arena.TARGET_BEGIN
        + "theorem demo : helper := by\n  trivial\n"
        + arena.TARGET_END
    )
    declaration, body = arena.extract_candidate_declaration(row, candidate)
    assert declaration == "theorem demo : helper := by\n  trivial"
    assert body == "by\n  trivial"

    changed = candidate.replace("theorem demo : helper", "theorem demo : True")
    with pytest.raises(arena.WorkflowError, match="exact signature"):
        arena.extract_candidate_declaration(row, changed)

def test_candidate_seed_uses_normalized_signature_and_original_body() -> None:
    row = sample_row()
    row["signature"] = "theorem demo (a b : Nat) : helper"
    row["src"] = "theorem demo (a : Nat) (b : Nat) : helper := by\n  trivial\n"
    assert arena.canonical_candidate_declaration(row) == (
        "theorem demo (a b : Nat) : helper := by\n  trivial\n"
    )
    assert arena.validate_supplied_declaration(row, row["src"]) == "by\n  trivial"
    with pytest.raises(arena.WorkflowError, match="exact signature"):
        arena.validate_declaration(row, row["src"])
    assert (
        arena.validate_declaration(row, arena.canonical_candidate_declaration(row))
        == "by\n  trivial"
    )
    assert arena.normalized_signature_example(row) == (
        "example (a b : Nat) : helper := by\n  apply demo <;> assumption"
    )

def test_candidate_seed_ignores_nested_assignment_by_in_statement() -> None:
    row = sample_row()
    row["signature"] = (
        "theorem demo (n : Nat) :\n"
        "  let f := fun (x : Fin n) => (show True from (by trivial))\n"
        "  let g := fun (x : Fin n) => id (p := by trivial) x\n"
        "  True"
    )
    row["src"] = row["signature"] + " := by\n  trivial\n"

    expected = len(row["signature"]) + 1
    assert arena.supplied_assignment_start(row) == expected
    assert arena.declaration_assignment_start(row["src"], row["name"]) == expected
    assert arena.validate_supplied_declaration(row, row["src"]) == "by\n  trivial"
    assert arena.canonical_candidate_declaration(row) == row["src"]

def test_candidate_seed_accepts_leading_theorem_attribute() -> None:
    row = sample_row()
    row["src"] = "@[grind]\ntheorem demo : helper := by\n  trivial\n"
    assert arena.validate_supplied_declaration(row, row["src"]) == "by\n  trivial"
    assert arena.canonical_candidate_declaration(row) == (
        "theorem demo : helper := by\n  trivial\n"
    )

def test_candidate_seed_accepts_scoped_open_and_qualified_name() -> None:
    row = sample_row()
    row["name"] = "Library.Namespace.Typing.progress"
    row["signature"] = "open OldExpressions in\nlemma Typing.progress : helper"
    row["src"] = (
        "open OldExpressions in\n"
        "lemma Typing.progress : helper := by\n  trivial\n"
    )

    assert arena.validate_supplied_declaration(row, row["src"]) == "by\n  trivial"
    assert arena.canonical_candidate_declaration(row) == row["src"]

def test_candidate_seed_rejects_executable_code_before_scoped_declaration() -> None:
    row = sample_row()
    row["src"] = (
        "def hidden : Nat := 1\n"
        "open OldExpressions in\n"
        "theorem demo : helper := by trivial"
    )

    with pytest.raises(arena.WorkflowError, match="unsupported code precedes"):
        arena.validate_supplied_declaration(row, row["src"])

def test_candidate_seed_preserves_scoped_open_then_target_attributes() -> None:
    row = sample_row()
    prefix = "open InterleavedCode in\n/-- Original theorem documentation. -/\n@[simp]\n"
    row["signature"] = prefix + "theorem demo : helper"
    row["src"] = row["signature"] + " := by\n  trivial\n"
    assert arena.validate_supplied_declaration(row, row["src"]) == "by\n  trivial"
    assert arena.canonical_candidate_declaration(row) == row["src"]
    assert not arena.supported_supplied_prefix(prefix + "#eval 1\n")
    assert not arena.supported_supplied_prefix(prefix + "axiom hidden : False\n")

def test_project_lemma_uses_qualified_benchmark_name() -> None:
    row = sample_row()
    row["name"] = "Outer.Inner.demo"
    row["signature"] = "lemma demo : helper"
    row["src"] = "lemma demo : helper := by trivial"
    assert arena.validate_supplied_declaration(row, row["src"]) == "by trivial"
    assert arena.canonical_candidate_declaration(row) == row["src"]

def test_project_compile_harness_replaces_only_target_declaration(
    tmp_path: Path,
) -> None:
    row = sample_row()
    row.update(
        {
            "name": "Outer.demo",
            "signature": "lemma demo : helper",
            "src": "lemma demo : helper := by trivial",
            "file_path": "Demo.lean",
        }
    )
    source = (
        "module\n\nimport Mathlib\n\npublic section\n\nnamespace Outer\n\n"
        "def helper : Prop := True\n\n/-- Target documentation. -/\n"
        "lemma demo : helper := by trivial\n\nlemma later : helper := demo\nend Outer\n"
    )
    (tmp_path / "Demo.lean").write_text(source, encoding="utf-8")
    candidate = "lemma demo : helper := by exact True.intro"

    quick = arena.project_compile_harness(row, candidate, tmp_path, exact=False)
    assert row["src"] not in quick
    assert candidate in quick
    assert "Target documentation" not in quick
    assert "lemma later : helper := demo" not in quick

    measured = arena.project_compile_harness(row, candidate, tmp_path, exact=True)
    assert "meta import LrhMeasurement" in measured
    assert "lrh_measured_decl lemma demo" in measured
    assert "lemma later : helper := demo" not in measured

def test_project_compile_harness_uses_helper_without_module_header(
    tmp_path: Path,
) -> None:
    row = sample_row()
    row.update(
        {
            "name": "Outer.demo",
            "signature": "lemma demo : helper",
            "src": "lemma demo : helper := by trivial",
            "file_path": "Demo.lean",
        }
    )
    (tmp_path / "Demo.lean").write_text(
        "import Mathlib\n\nnamespace Outer\n\ndef helper : Prop := True\n\n"
        "lemma demo : helper := by trivial\n",
        encoding="utf-8",
    )

    measured = arena.project_compile_harness(
        row,
        "lemma demo : helper := by exact True.intro",
        tmp_path,
        exact=True,
    )

    assert measured.startswith("import LrhMeasurement\nimport Mathlib")
    assert "lrh_measured_decl lemma demo" in measured
    assert "#count_heartbeats in" not in measured
    assert not arena.project_source_has_module_header(row, tmp_path)

def test_project_compile_harness_accepts_compatibility_proof_body_drift(
    tmp_path: Path,
) -> None:
    row = sample_row()
    row.update(
        {
            "name": "Outer.demo",
            "signature": "lemma demo : helper",
            "src": "lemma demo : helper := by trivial",
            "file_path": "Demo.lean",
        }
    )
    (tmp_path / "Demo.lean").write_text(
        "import Mathlib\n\nnamespace Outer\n\ndef helper : Prop := True\n\n"
        "lemma demo : helper := by exact True.intro\n",
        encoding="utf-8",
    )
    candidate = "lemma demo : helper := by simpa using True.intro"

    harness = arena.project_compile_harness(
        row, candidate, tmp_path, exact=False
    )

    assert candidate in harness
    assert "by exact True.intro" not in harness

def test_project_compile_harness_replaces_scoped_qualified_declaration_once(
    tmp_path: Path,
) -> None:
    row = sample_row()
    row.update(
        {
            "name": "Library.Namespace.Typing.progress",
            "signature": "open OldExpressions in\nlemma Typing.progress : helper",
            "src": (
                "open OldExpressions in\n"
                "lemma Typing.progress : helper := by trivial"
            ),
            "file_path": "Demo.lean",
        }
    )
    (tmp_path / "Demo.lean").write_text(
        "import Mathlib\n\ndef helper : Prop := True\n\n"
        "open OldExpressions in\n"
        "lemma Typing.progress : helper := by exact True.intro\n",
        encoding="utf-8",
    )
    candidate = (
        "open OldExpressions in\n"
        "lemma Typing.progress : helper := by simpa using True.intro"
    )

    harness = arena.project_compile_harness(row, candidate, tmp_path, exact=False)

    assert harness.count("open OldExpressions in") == 1
    assert harness.count("lemma Typing.progress") == 1
    assert candidate in harness
    assert "by exact True.intro" not in harness

def test_project_compile_harness_rejects_scoped_prefix_drift(tmp_path: Path) -> None:
    row = sample_row()
    row.update(
        {
            "name": "Outer.demo",
            "signature": "open Expected in\ntheorem demo : helper",
            "src": "open Expected in\ntheorem demo : helper := by trivial",
            "file_path": "Demo.lean",
        }
    )
    (tmp_path / "Demo.lean").write_text(
        "import Mathlib\n\nopen Changed in\ntheorem demo : helper := by trivial\n",
        encoding="utf-8",
    )

    with pytest.raises(arena.WorkflowError, match="scoped prefix"):
        arena.project_compile_harness(
            row,
            "open Expected in\ntheorem demo : helper := by exact True.intro",
            tmp_path,
            exact=False,
        )

def test_project_compile_harness_rejects_ambiguous_qualified_suffix(
    tmp_path: Path,
) -> None:
    row = sample_row()
    row.update(
        {
            "name": "Library.Typing.progress",
            "signature": "lemma Typing.progress : helper",
            "src": "lemma Typing.progress : helper := by trivial",
            "file_path": "Demo.lean",
        }
    )
    (tmp_path / "Demo.lean").write_text(
        "import Mathlib\n\ndef helper : Prop := True\n\n"
        "lemma Other.progress : helper := by trivial\n"
        "lemma Typing.progress : helper := by exact True.intro\n",
        encoding="utf-8",
    )

    with pytest.raises(arena.WorkflowError, match="found 2"):
        arena.project_compile_harness(
            row,
            "lemma Typing.progress : helper := by simpa using True.intro",
            tmp_path,
            exact=False,
        )

def test_project_compile_harness_rejects_compatibility_statement_drift(
    tmp_path: Path,
) -> None:
    row = sample_row()
    row.update(
        {
            "name": "Outer.demo",
            "signature": "lemma demo : helper",
            "src": "lemma demo : helper := by trivial",
            "file_path": "Demo.lean",
        }
    )
    (tmp_path / "Demo.lean").write_text(
        "import Mathlib\n\nnamespace Outer\n\ndef helper : Prop := True\n\n"
        "lemma demo : True := by trivial\n",
        encoding="utf-8",
    )

    with pytest.raises(arena.WorkflowError, match="theorem statement changed"):
        arena.project_compile_harness(
            row,
            "lemma demo : helper := by exact True.intro",
            tmp_path,
            exact=False,
        )

def test_forbidden_proof_constructs_are_rejected() -> None:
    row = sample_row()
    with pytest.raises(arena.WorkflowError, match="sorry"):
        arena.validate_declaration(row, "theorem demo : helper := by sorry")
    with pytest.raises(arena.WorkflowError, match="extra top-level"):
        arena.validate_declaration(
            row,
            "theorem demo : helper := by trivial\n"
            "theorem hiddenHelper : True := by trivial",
        )


def test_exact_heartbeat_wrapper_overrides_global_unlimited_cap() -> None:
    row = sample_row()
    row["header"] = "import Mathlib\n\nset_option maxHeartbeats 0\n\n"
    rendered = arena.exact_heartbeat_audit_harness(
        row, "theorem demo : helper := by trivial"
    )
    assert "set_option maxHeartbeats 0" in rendered
    assert "set_option Elab.async false in\n" in rendered
    assert "set_option maxHeartbeats 1000000000 in\n#count_heartbeats in\n" in rendered
    assert rendered.endswith("#print axioms demo\n")

def test_exact_heartbeat_parser_is_strict() -> None:
    assert (
        arena.parse_exact_heartbeat_count(
            "Used 39 heartbeats, which is less than the current maximum of 1000000000."
        )
        == 39
    )
    assert (
        arena.parse_exact_heartbeat_count(
            "Used 41 heartbeats, which is greater than the current maximum of 10."
        )
        == 41
    )
    with pytest.raises(arena.WorkflowError, match="exactly one positive"):
        arena.parse_exact_heartbeat_count("no count here")
    with pytest.raises(arena.WorkflowError, match="exactly one positive"):
        arena.parse_exact_heartbeat_count(
            "Used 1 heartbeats, which is less than the current maximum of 10.\n"
            "Used 2 heartbeats, which is less than the current maximum of 10."
        )

def test_project_heartbeat_parser_is_strict() -> None:
    assert arena.parse_project_heartbeat_count("LRH_HEARTBEATS 4251") == 4251
    with pytest.raises(arena.WorkflowError, match="exactly one"):
        arena.parse_project_heartbeat_count("LRH_HEARTBEATS 1\nLRH_HEARTBEATS 2")

def test_evaluation_scratch_directory_uses_short_configured_root(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    scratch_parent = tmp_path / "short"
    monkeypatch.setenv("LEAN_REFACTOR_SCRATCH_ROOT", str(scratch_parent))

    with arena.temporary_evaluation_directory("lrh-pq-") as temporary:
        scratch = Path(temporary)
        assert scratch.parent == scratch_parent.resolve()
        assert scratch.name.startswith("lrh-pq-")

    assert not scratch.exists()


def test_axiom_parser_accepts_only_standard_logical_axioms() -> None:
    output = "'demo' depends on axioms: [propext, Classical.choice, Quot.sound]"
    assert arena.parse_and_validate_axioms("demo", output) == [
        "propext",
        "Classical.choice",
        "Quot.sound",
    ]

    with pytest.raises(arena.WorkflowError, match="unexpected"):
        arena.parse_and_validate_axioms(
            "demo", "'demo' depends on axioms: [Classical.choice, customAxiom]"
        )


def test_current_arena_row_is_normalized_to_one_declaration() -> None:
    raw = {
        "name": "demo",
        "statement": "theorem demo : True",
        "src": "theorem demo : True := by trivial",
        "proof_length": 4,
    }
    row = arena.normalize_arena_row(raw)
    assert row["signature"] == raw["statement"]
    assert row["contexts"] == []
    assert arena.canonical_candidate_declaration(row) == raw["src"]

def test_local_token_proxy_ignores_comments_but_counts_syntax() -> None:
    verbose = "by\n  -- ignored words here\n  exact True.intro"
    compact = "by exact True.intro"
    assert arena.local_proof_tokens(verbose) == arena.local_proof_tokens(compact)
    assert arena.local_proof_tokens(compact) == ["by", "exact", "True.intro"]

def test_passing_candidate_checkpoint_is_content_addressed(tmp_path: Path) -> None:
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text("theorem demo : True := by trivial\n", encoding="utf-8")
    evaluation = arena.Evaluation(
        task_id="demo",
        candidate_path=str(candidate),
        valid=True,
        compile_seconds=1.0,
        axiom_audit_seconds=None,
        axioms=[],
        original_local_tokens=5,
        candidate_local_tokens=3,
        local_token_reduction_pct=40.0,
        official_original_tokens=None,
    )
    first = arena.checkpoint_candidate(candidate, evaluation, tmp_path / "valid")
    second = arena.checkpoint_candidate(candidate, evaluation, tmp_path / "valid")
    assert first == second
    assert first.name.startswith("000003-")
    assert first.read_text(encoding="utf-8") == candidate.read_text(encoding="utf-8")


def test_quick_payload_does_not_claim_unmeasured_axioms_or_heartbeats() -> None:
    evaluation = arena.Evaluation(
        task_id="demo",
        candidate_path="Candidate.lean",
        valid=True,
        compile_seconds=1.0,
        axiom_audit_seconds=None,
        axioms=None,
        original_local_tokens=100,
        candidate_local_tokens=20,
        local_token_reduction_pct=80.0,
        official_original_tokens=100,
    )
    payload = arena.evaluation_payload(evaluation)
    assert payload["measurement_mode"] == "quick"
    assert payload["axioms"] is None
    assert payload["axiom_status"] == "not_run"
    assert payload["heartbeat"]["status"] == "not_run"
    assert payload["local_two_axis_mean"] is None

@contextmanager
def live_child_cache_lock(path: Path):
    """Hold a real open lock descriptor in an independent Python process."""
    child_code = (
        "import os, sys; from pathlib import Path; sys.path.insert(0, sys.argv[1]); "
        "import arena_workflow as arena\n"
        "with arena.exclusive_file_lock(Path(sys.argv[2]), 2, "
        "request={'test': 'owner'}):\n"
        " print('ready', os.getpid(), flush=True)\n"
        " sys.stdin.read(1)\n"
    )
    owner = subprocess.Popen(
        [sys.executable, "-c", child_code, str(SCRIPT.parent), str(path)],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        assert owner.stdout is not None
        ready = owner.stdout.readline().split()
        assert len(ready) == 2 and ready[0] == "ready"
        # Windows Python launchers may spawn the interpreter under another PID.
        yield owner, int(ready[1])
    finally:
        try:
            owner.communicate(input="\n", timeout=10)
        except subprocess.TimeoutExpired:
            owner.kill()
            owner.communicate(timeout=10)
        assert owner.returncode == 0


def test_cache_lock_recovers_dead_owner_and_cleans_body_failure(tmp_path: Path) -> None:
    exited = subprocess.run(
        [sys.executable, "-c", "import os; print(os.getpid())"],
        check=True, capture_output=True, text=True, timeout=10,
    )
    path = tmp_path / "orphan.lock"
    path.write_text(json.dumps({"pid": int(exited.stdout)}), encoding="utf-8")
    with (
        pytest.raises(ValueError, match="body failure"),
        arena.exclusive_file_lock(path, 1),
    ):
        assert json.loads(path.read_text())["pid"] == os.getpid()
        raise ValueError("body failure")
    assert not path.exists()
    with arena.exclusive_file_lock(path, 1):
        pass
    assert not path.exists()


def test_evaluation_cache_infrastructure_error_is_not_timeout_or_cached(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    task, candidate = write_sample_task_and_candidate(tmp_path)
    cache = tmp_path / "cache"
    monkeypatch.setenv("LEAN_REFACTOR_EVALUATION_CACHE", str(cache))
    monkeypatch.setattr(arena, "measurement_environment_fingerprint", lambda *_a: "a" * 64)
    events: list[dict[str, object]] = []
    monkeypatch.setattr(arena, "record_event", lambda kind, data: events.append({"kind": kind, **data}))

    def fail_evaluation(*_args, **_kwargs):
        raise OSError("controlled infrastructure failure")

    monkeypatch.setattr(arena, "_evaluate_candidate_uncached", fail_evaluation)
    with pytest.raises(OSError, match="controlled infrastructure failure"):
        arena.evaluate_candidate(task, candidate, tmp_path)
    assert events[-1]["error_kind"] == "infrastructure"
    assert events[-1]["cache_lock"]["status"] == "acquired"
    assert not list(cache.rglob("*.json"))
    assert not list(cache.rglob("*.lock"))

def test_exact_evaluation_cache_subsumes_quick_and_deduplicates_waiters(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    task, candidate = write_sample_task_and_candidate(tmp_path)
    cache = tmp_path / "cache"
    monkeypatch.setenv("LEAN_REFACTOR_EVALUATION_CACHE", str(cache))
    monkeypatch.setattr(
        arena, "measurement_environment_fingerprint", lambda *_args: "a" * 64
    )
    calls: list[bool] = []

    def fake_evaluate(
        _task: Path,
        candidate_path: Path,
        _root: Path,
        timeout_seconds: int = 600,
        quick: bool = False,
        environment_fingerprint: str | None = None,
        **_kwargs,
    ) -> arena.Evaluation:
        del timeout_seconds
        calls.append(quick)
        time.sleep(0.05)
        return arena.Evaluation(
            task_id="demo",
            candidate_path=str(candidate_path),
            valid=True,
            compile_seconds=1.0,
            axiom_audit_seconds=0.5,
            axioms=[],
            original_local_tokens=5,
            candidate_local_tokens=4,
            local_token_reduction_pct=20.0,
            official_original_tokens=5,
            environment_fingerprint=environment_fingerprint,
            heartbeat=100,
            heartbeat_reduction_pct=90.0,
        )

    monkeypatch.setattr(arena, "_evaluate_candidate_uncached", fake_evaluate)
    with ThreadPoolExecutor(max_workers=4) as executor:
        exact = list(
            executor.map(
                lambda _: arena.evaluate_candidate(task, candidate, tmp_path),
                range(4),
            )
        )
    assert len(exact) == 4
    assert calls == [False]

    quick = arena.evaluate_candidate(task, candidate, tmp_path, quick=True)
    assert calls == [False]
    assert quick.heartbeat is None
    assert quick.axioms is None
    assert quick.candidate_path == str(candidate.resolve())

def write_project_resident_task_and_candidate(tmp_path: Path) -> tuple[Path, Path]:
    row = sample_row()
    row["file_path"] = "Demo.lean"
    (tmp_path / "Demo.lean").write_text(
        arena.render_environment(row) + str(row["src"]) + "\n",
        encoding="utf-8",
    )
    task = tmp_path / "Task.json"
    task.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "reference": {"heartbeat": 1000},
                "local_baselines": [],
                "row": row,
            }
        ),
        encoding="utf-8",
    )
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text(
        arena.render_environment(row)
        + arena.TARGET_BEGIN
        + "theorem demo : helper := by\n  exact True.intro\n"
        + arena.TARGET_END,
        encoding="utf-8",
    )
    return task, candidate

def configure_fake_persistent_broker(
    root: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv(arena.PERSISTENT_QUICK_ENDPOINT_ENV, "127.0.0.1:12345")
    monkeypatch.setenv(arena.PERSISTENT_QUICK_TOKEN_ENV, "test-token")
    monkeypatch.setenv(arena.PERSISTENT_QUICK_PROJECT_ROOT_ENV, str(root))

@pytest.mark.parametrize("project_resident", [False, True])
def test_broker_setup_preserves_quick_source_and_provisions_support_once(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, project_resident: bool
) -> None:
    task, _candidate = (
        write_project_resident_task_and_candidate(tmp_path)
        if project_resident
        else write_sample_task_and_candidate(tmp_path)
    )
    _, row = arena.load_task(task)
    support = tmp_path / "cached-helper" if project_resident else None
    preparations: list[tuple[dict, Path, int]] = []
    broker_args: list[dict[str, object]] = []

    def prepare(observed_row, root, timeout):
        preparations.append((observed_row, root, timeout))
        return support

    class FakeBroker:
        def __init__(self, root, work_root, source, **kwargs):
            broker_args.append(
                {"root": root, "work_root": work_root, "source": source, **kwargs}
            )
            self.started = False
            self.ready = False

        def start(self):
            self.started = True

        def prewarm(self, *, timeout_seconds):
            assert self.started
            assert 0 < timeout_seconds <= 600
            self.ready = True
            return {"ready": True, "valid": False}

        def environment(self):
            assert self.ready
            return {
                arena.PERSISTENT_QUICK_PROJECT_ROOT_ENV: str(tmp_path),
                capsule_tools.persistent_quick.FEEDBACK_SUPPORT_ENV: json.dumps(
                    [str(support)] if support else []
                ),
            }

    monkeypatch.setattr(capsule_tools.advisory_feedback, "prepare_support", prepare)
    monkeypatch.setattr(capsule_tools.persistent_quick, "PersistentQuickBroker", FakeBroker)
    for key in (
        arena.PERSISTENT_QUICK_PROJECT_ROOT_ENV,
        capsule_tools.persistent_quick.FEEDBACK_SUPPORT_ENV,
    ):
        monkeypatch.setenv(key, "prior")
    broker = capsule_tools.start_quick_broker(row, tmp_path, tmp_path / "broker", 15)
    assert broker.started is True
    assert preparations[0][:2] == (row, tmp_path)
    assert 0 < preparations[0][2] <= 600
    assert broker_args[0]["timeout_seconds"] == 15
    assert broker_args[0]["startup_timeout_seconds"] == 600
    assert broker_args[0]["lean_path_prefixes"] == ([support] if support else None)
    source = broker_args[0]["source"]
    assert source.count("def helper : Prop := True") == 1
    assert source.count("theorem demo : helper") == 1
    assert "#count_heartbeats" not in source and "LrhMeasurement" not in source
    assert os.environ[arena.PERSISTENT_QUICK_PROJECT_ROOT_ENV] == str(tmp_path)
    assert json.loads(os.environ[capsule_tools.persistent_quick.FEEDBACK_SUPPORT_ENV]) == (
        [str(support)] if support else []
    )
    setup = json.loads((tmp_path / "broker" / "setup.json").read_text())
    assert setup["status"] == "ready"
    assert setup["readiness"]["valid"] is False

def test_broker_startup_failure_closes_before_environment_export(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    closed = []
    monkeypatch.setattr(capsule_tools.advisory_feedback, "prepare_support", lambda *_: None)

    class FakeBroker:
        def __init__(self, *_args, **_kwargs):
            pass

        def start(self):
            pass

        def prewarm(self, **_kwargs):
            raise capsule_tools.persistent_quick.PersistentQuickError("startup timed out")

        def environment(self):
            pytest.fail("failed startup must not be exported to an agent")

        def close(self):
            closed.append(True)

    monkeypatch.setattr(capsule_tools.persistent_quick, "PersistentQuickBroker", FakeBroker)
    monkeypatch.setenv(arena.PERSISTENT_QUICK_ENDPOINT_ENV, "previous-broker")
    with pytest.raises(capsule_tools.persistent_quick.PersistentQuickError, match="startup timed out"):
        capsule_tools.start_quick_broker(sample_row(), tmp_path, tmp_path / "broker", 15)
    assert closed == [True]
    assert os.environ[arena.PERSISTENT_QUICK_ENDPOINT_ENV] == "previous-broker"
    setup = json.loads((tmp_path / "broker" / "setup.json").read_text())
    assert setup["status"] == "failed"
    assert setup["failure_phase"] == "prewarm"

def test_broker_support_and_prewarm_share_startup_budget(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    clock = [10.0]
    budgets = []
    monkeypatch.setattr(capsule_tools.time, "monotonic", lambda: clock[0])

    def prepare(_row, _root, budget):
        assert budget == 120
        clock[0] += 25

    class FakeBroker:
        def __init__(self, *_args, **_kwargs):
            pass

        def start(self):
            clock[0] += 5

        def prewarm(self, *, timeout_seconds):
            budgets.append(timeout_seconds)
            return {"ready": True}

        def environment(self):
            return {}

    monkeypatch.setattr(capsule_tools.advisory_feedback, "prepare_support", prepare)
    monkeypatch.setattr(capsule_tools.persistent_quick, "PersistentQuickBroker", FakeBroker)
    capsule_tools.start_quick_broker(
        sample_row(), tmp_path, tmp_path / "broker", 15, startup_timeout_seconds=120,
    )
    assert budgets == [90]


@pytest.mark.parametrize("timed_out", [False, True])
def test_require_lean_success_preserves_typed_failure_and_result(timed_out: bool) -> None:
    result = arena.LeanRun(
        ["lean", "private.lean"], 1, 2.5, "example compiler diagnostic",
        timed_out=timed_out, log_path="private.log",
    )
    expected = arena.LeanTimeoutError if timed_out else arena.LeanCompileError
    with pytest.raises(expected) as caught:
        arena.require_lean_success(result, "test compile")
    assert isinstance(caught.value, arena.WorkflowError)
    assert caught.value.result is result
    if timed_out:
        assert str(caught.value) == "test compile exceeded 2.5 seconds"
    else:
        assert str(caught.value) == (
            "test compile failed with exit 1\nexample compiler diagnostic\n"
            "full Lean log: private.log"
        )

@pytest.mark.parametrize("project_resident", [False, True])
def test_quick_evaluation_uses_persistent_broker_without_cold_lean(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, project_resident: bool
) -> None:
    task, candidate = (
        write_project_resident_task_and_candidate(tmp_path)
        if project_resident
        else write_sample_task_and_candidate(tmp_path)
    )
    configure_fake_persistent_broker(tmp_path, monkeypatch)
    monkeypatch.setattr(
        arena,
        "run_lean",
        lambda *_args, **_kwargs: pytest.fail("cold Lean was launched"),
    )
    observed_sources: list[str] = []

    def request(source: str, _timeout: int) -> dict[str, object]:
        observed_sources.append(source)
        return {
            "ok": True,
            "valid": True,
            "diagnostics": [],
            "wall_seconds": 1.2,
            "lsp_seconds": 1.0,
            "working_set_bytes": 1234,
        }

    monkeypatch.setattr(arena, "persistent_quick_request", request)

    evaluation = arena._evaluate_candidate_uncached(
        task,
        candidate,
        tmp_path,
        quick=True,
        environment_fingerprint="a" * 64,
    )

    assert evaluation.valid is True
    assert evaluation.compile_seconds == 1.2
    assert len(observed_sources) == 1
    source = observed_sources[0]
    assert source.startswith("import Mathlib\n\n")
    assert source.count("def helper : Prop := True") == 1
    assert source.count("theorem demo : helper") == 1
    assert arena.TARGET_BEGIN not in source and arena.TARGET_END not in source
    assert "#count_heartbeats" not in source and "lrh_measured_decl" not in source
    assert "#print axioms" not in source

@pytest.mark.parametrize("project_resident", [False, True])
def test_persistent_quick_infrastructure_failure_falls_back_to_cold_lean(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, project_resident: bool
) -> None:
    task, candidate = (
        write_project_resident_task_and_candidate(tmp_path)
        if project_resident
        else write_sample_task_and_candidate(tmp_path)
    )
    configure_fake_persistent_broker(tmp_path, monkeypatch)
    monkeypatch.setattr(
        arena,
        "persistent_quick_request",
        lambda *_args: (_ for _ in ()).throw(arena.PersistentQuickFailure(
            arena.broker_client.BrokerClientError("transport_failed", "broker down", retryable=True))),
    )
    calls: list[Path] = []

    def fake_run_lean(
        path: Path,
        _root: Path,
        _timeout: int,
        **_kwargs: object,
    ) -> arena.LeanRun:
        calls.append(path)
        assert "theorem demo" in path.read_text(encoding="utf-8")
        return arena.LeanRun(["lean"], 0, 2.5, "")

    monkeypatch.setattr(arena, "run_lean", fake_run_lean)
    evaluation = arena._evaluate_candidate_uncached(
        task,
        candidate,
        tmp_path,
        quick=True,
        environment_fingerprint="b" * 64,
    )

    assert evaluation.valid is True
    assert evaluation.compile_seconds == 2.5
    assert len(calls) == 1
    if not project_resident:
        assert calls[0] != candidate  # Cold Lean receives the admitted snapshot.

@pytest.mark.parametrize("project_resident", [False, True])
def test_persistent_quick_candidate_error_does_not_trigger_cold_fallback(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, project_resident: bool
) -> None:
    task, candidate = (
        write_project_resident_task_and_candidate(tmp_path)
        if project_resident
        else write_sample_task_and_candidate(tmp_path)
    )
    configure_fake_persistent_broker(tmp_path, monkeypatch)
    monkeypatch.setattr(
        arena,
        "persistent_quick_request",
        lambda *_args: {
            "ok": True,
            "valid": False,
            "diagnostics": [
                {
                    "severity": "error",
                    "line": 4,
                    "character": 2,
                    "message": "synthetic candidate error",
                }
            ],
            "wall_seconds": 1.1,
            "lsp_seconds": 1.0,
            "working_set_bytes": 1234,
        },
    )
    monkeypatch.setattr(
        arena,
        "run_lean",
        lambda *_args, **_kwargs: pytest.fail("candidate error triggered cold Lean"),
    )

    with pytest.raises(arena.LeanCompileError, match="synthetic candidate error"):
        arena._evaluate_candidate_uncached(
            task,
            candidate,
            tmp_path,
            quick=True,
            environment_fingerprint="c" * 64,
        )

def test_cached_measurement_helper_is_built_once_and_integrity_checked(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("LEAN_REFACTOR_EVALUATION_CACHE", str(tmp_path / "cache"))
    calls: list[Path] = []

    def fake_run_lean(
        path: Path,
        _root: Path,
        _timeout: int,
        *,
        lean_args: list[str] | None = None,
        lean_path_prefixes: list[Path] | None = None,
    ) -> arena.LeanRun:
        del lean_path_prefixes
        calls.append(path)
        assert lean_args is not None
        output = Path(lean_args[lean_args.index("-o") + 1])
        output.write_bytes(b"compiled helper")
        return arena.LeanRun(["lean"], 0, 0.1, "")

    monkeypatch.setattr(arena, "run_lean", fake_run_lean)
    first = arena.cached_project_measurement_helper(tmp_path, 10, "b" * 64)
    second = arena.cached_project_measurement_helper(tmp_path, 10, "b" * 64)
    assert first == second
    assert len(calls) == 1

    assert first is not None
    (first / "LrhMeasurement.olean").write_bytes(b"corrupted")
    arena.cached_project_measurement_helper(tmp_path, 10, "b" * 64)
    assert len(calls) == 2


def test_explicit_fingerprint_registry_avoids_version_process_and_guards_inputs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    row = sample_row()
    project = tmp_path / "project"
    project.mkdir()
    (project / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.test\n", encoding="utf-8"
    )
    registry_path = tmp_path / "fingerprints.json"
    monkeypatch.setattr(
        arena,
        "recorded_lean_version",
        lambda *_args: "Lean (version 4.test, synthetic)",
    )

    fingerprints = arena.write_environment_fingerprint_registry(
        row, [project], registry_path
    )
    key = arena.environment_fingerprint_registry_key(row, project)
    expected = fingerprints[key]
    monkeypatch.setattr(
        arena,
        "recorded_lean_version",
        lambda *_args: pytest.fail("explicit lookup reran the Lean version process"),
    )

    assert (
        arena.measurement_environment_fingerprint(
            row, project, registry_path=registry_path
        )
        == expected
    )
    entry = arena.environment_fingerprint_registry_entry(
        row, project, registry_path, validate_guard=True
    )
    assert entry["lean_version"] == "Lean (version 4.test, synthetic)"

    (project / "lake-manifest.json").write_text(
        '{"changed": true}\n', encoding="utf-8"
    )
    with pytest.raises(arena.WorkflowError, match="registry entry is stale"):
        arena.measurement_environment_fingerprint(
            row, project, registry_path=registry_path
        )

def test_explicit_fingerprint_registry_rejects_missing_task_entry(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    row = sample_row()
    project = tmp_path / "project"
    project.mkdir()
    (project / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
    registry_path = tmp_path / "fingerprints.json"
    monkeypatch.setattr(arena, "recorded_lean_version", lambda *_args: "Lean 4.test")
    arena.write_environment_fingerprint_registry(row, [project], registry_path)
    other = dict(row)
    other["name"] = "other"

    with pytest.raises(arena.WorkflowError, match="has no entry"):
        arena.measurement_environment_fingerprint(
            other, project, registry_path=registry_path
        )


def test_file_permit_pool_caps_concurrency_across_waiters(tmp_path: Path) -> None:
    pool = resource_gate.FilePermitPool(
        tmp_path, "lean", 2, poll_seconds=0.01
    )
    active = 0
    maximum = 0

    def occupy(_index: int) -> float:
        nonlocal active, maximum
        with pool.acquire(timeout_seconds=5) as lease:
            active += 1
            maximum = max(maximum, active)
            time.sleep(0.04)
            active -= 1
            return lease.queue_wait_seconds

    with ThreadPoolExecutor(max_workers=4) as executor:
        waits = list(executor.map(occupy, range(4)))

    assert maximum == 2
    assert sum(wait > 0.02 for wait in waits) >= 2
    assert not list((tmp_path / "lean" / "holders").glob("*.json"))
    assert not list((tmp_path / "lean" / "requests").glob("*.request"))


@pytest.mark.parametrize("quick", [False, True])
def test_public_fresh_evaluation_compiles_each_request_without_result_cache(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, quick: bool
) -> None:
    from lean_tools.evaluation import evaluate_candidate_fresh

    task, candidate = write_sample_task_and_candidate(tmp_path)
    cache = tmp_path / "result-cache"
    monkeypatch.setenv("LEAN_REFACTOR_EVALUATION_CACHE", str(cache))
    for name in (
        arena.PERSISTENT_QUICK_ENDPOINT_ENV,
        arena.PERSISTENT_QUICK_TOKEN_ENV,
        arena.PERSISTENT_QUICK_PROJECT_ROOT_ENV,
    ):
        monkeypatch.delenv(name, raising=False)
    compiled = []

    def run(path, _project, timeout):
        assert timeout == 17
        compiled.append(path.read_text(encoding="utf-8"))
        return arena.LeanRun(
            ["lean"], 0, 0.25,
            "Used 23 heartbeats, which is less than the current maximum of 1000000000.\n"
            "'demo' does not depend on any axioms\n",
        )

    monkeypatch.setattr(arena, "run_lean", run)
    monkeypatch.setattr(
        arena, "measurement_environment_fingerprint",
        lambda *_: pytest.fail("supplied fingerprint was ignored"),
    )
    results = [
        evaluate_candidate_fresh(
            task, candidate, tmp_path, timeout_seconds=17, quick=quick,
            environment_fingerprint="d" * 64,
        )
        for _ in range(2)
    ]
    assert len(compiled) == 2
    assert compiled[0] == compiled[1]
    assert not cache.exists()
    for result in results:
        payload = arena.evaluation_payload(result)
        assert payload["cache"] == {"status": "disabled", "hit": False, "source_mode": None}
        assert payload["timing"]["measurement_source"] == "current_request"
        assert result.request_wall_seconds is not None
        assert result.heartbeat == (None if quick else 23)
        assert result.axioms == (None if quick else [])

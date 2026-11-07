"""Compiler rejection evidence and native selection before the output cap."""
from types import SimpleNamespace

import pytest

from e6 import deterministic_native as native
from e6.deterministic_support import search_cache, search_policy
from lean_tools import arena_workflow as arena


def failure(output, *, returncode=1, timed_out=False, stage="measured project compile",
            command=None):
    result = SimpleNamespace(output=output, returncode=returncode, timed_out=timed_out)
    if command is not None:
        result.command = command
    return arena.LeanCompileError(f"Task.target: {stage} failed with exit {returncode}", result)


@pytest.mark.parametrize("code", [None, "lean.unknownIdentifier", "lean.typeMismatch",
                                  "lean.unsolvedGoals", "future.diagnostic_42"])
def test_positioned_ordinary_diagnostics_accept_lean_versions_with_or_without_codes(code):
    suffix = "" if code is None else f"({code})"
    error = failure(f"/scratch/Candidate.lean:12:3: error{suffix}: invalid proof",
                    command=["lean", "/scratch/Candidate.lean"])
    receipt = search_cache.compile_rejection(error, arena.LeanCompileError)
    assert receipt["kind"] == "lean_compile_invalid"
    assert receipt["diagnostic_codes"] == ([] if code is None else [code])


@pytest.mark.parametrize("output", [
    "error(lean.unknownIdentifier): unknown identifier",
    "Candidate.lean:2:0: warning: text contains error(lean.unknownIdentifier):",
    "compiler wrapper: error: crashed",
    "/dependency/Other.lean:3:0: error(lean.unknownIdentifier): unknown identifier",
])
def test_unpositioned_warning_wrapper_or_unrelated_source_is_not_negative_evidence(output):
    error = failure(output, command=["lean", "Candidate.lean"])
    assert search_cache.compile_rejection(error, arena.LeanCompileError) is None


@pytest.mark.parametrize("kwargs", [
    {"returncode": 0}, {"returncode": -9}, {"returncode": 137}, {"returncode": True},
    {"timed_out": True}, {"timed_out": None}, {"stage": "measurement helper"},
    {"stage": "project axiom audit"}, {"stage": "resolved project compile"},
    {"command": ["lean", "Helper.lean"]}, {"command": "lean Candidate.lean"},
])
def test_typed_diagnostic_does_not_override_strict_launch_and_stage_evidence(kwargs):
    error = failure("Candidate.lean:1:0: error(lean.unknownIdentifier): unknown name", **kwargs)
    assert search_cache.compile_rejection(error, arena.LeanCompileError) is None


@pytest.mark.parametrize("marker", [
    "maximum number of heartbeats", "maxHeartbeats", "maxRecDepth", "deepRecursion",
    "maximum recursion depth", "timeout", "out of memory", "interrupted", "cancelled",
    "canceled", "resource exhausted", "stack overflow", "unknown module prefix",
    "no such file", "permission denied", "failed to open file",
    "failed to load dynamic library", "object file", "lean.unknownModule", "lean.unknownPackage",
])
def test_typed_errors_keep_resource_and_environment_failures_retryable(marker):
    error = failure(f"Candidate.lean:1:0: error(lean.unknownIdentifier): unknown name\n{marker}")
    assert search_cache.compile_rejection(error, arena.LeanCompileError) is None


@pytest.mark.parametrize("code", ["lean.unknownModule", "lean.unknownModulePrefix", "lean.unknownPackage"])
def test_typed_missing_import_diagnostic_is_not_proof_invalidity(code):
    error = failure(f"Candidate.lean:1:0: error({code}): import unavailable",
                    command=["lean", "Candidate.lean"])
    assert search_cache.compile_rejection(error, arena.LeanCompileError) is None


def crowded_inventory():
    tactics = [f"simp only [rule{i}, other{i}]" for i in range(50)]
    source = "theorem target : True := by\n  " + "\n  ".join(tactics)
    children = []
    for tactic in tactics:
        start = source.index(tactic)
        children.append({"start_byte": start, "end_byte": start + len(tactic)})
    scan = {"proof_start_byte": source.index("by"), "declaration_end_byte": len(source),
            "terms": [], "sequences": [{"start_byte": children[0]["start_byte"],
                "end_byte": children[-1]["end_byte"], "children": children}]}
    return source, scan


def test_priorities_refill_from_after_legacy_cap_with_stable_candidate_identity():
    source, scan = crowded_inventory()
    legacy = native.proposals_from_inventory(source, scan, max_candidates=128)
    summary = {}
    selected = native.proposals_from_inventory(source, scan, max_candidates=128,
        policy="prioritized", policy_maximum=256, inventory_summary=summary)
    old = search_policy.order_candidates(legacy, policy="prioritized", maximum=256)
    assert len(selected) == 128 and len(selected) > len(old)
    assert summary["bounded_candidate_count"] > 128
    assert any(int(item["id"].removeprefix("native-")) >= 128 for item in selected)
    by_hash = {item["source_sha256"]: item for item in legacy}
    for item in selected:
        if item["source_sha256"] in by_hash:
            assert item == by_hash[item["source_sha256"]]
    assert sum(item["family"] in search_policy.WINDOW_FAMILIES for item in selected) <= 8
    assert native.proposals_from_inventory(source, scan, max_candidates=128) == legacy


def test_native_output_cap_does_not_shrink_parent_exploration_quota():
    source, scan = crowded_inventory()
    selected = native.proposals_from_inventory(source, scan, max_candidates=128,
        policy="prioritized", policy_maximum=256)
    assert sum(item["family"] in search_policy.WINDOW_FAMILIES for item in selected) > 4
    assert len({item["source_sha256"] for item in selected}) == len(selected)


@pytest.mark.parametrize("kwargs", [
    {"policy": "missing"}, {"policy": "prioritized", "policy_maximum": 64},
    {"policy": "prioritized", "policy_maximum": True},
    {"policy": "prioritized", "policy_maximum": 4097},
])
def test_invalid_native_policy_bounds_are_rejected(kwargs):
    source, scan = crowded_inventory()
    with pytest.raises(ValueError):
        native.proposals_from_inventory(source, scan, **kwargs)

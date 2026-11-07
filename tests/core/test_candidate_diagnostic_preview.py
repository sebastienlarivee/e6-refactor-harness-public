"""Brief candidate failures retain actionable goals without changing full evidence."""
from __future__ import annotations

import pytest

from lean_tools import candidate_batches as batches

arena = batches.arena

# PH pass 4, `only_three`: the old twelve-line prefix ended at tieLeft.
PH_TARGET = (
    "⊢ t • (x * ι (ofCrAnListF [φ, ψ]) * y - s • x * ι (ofCrAnListF [ψ, φ]) * y) =\n"
    "    t • (x * ι (ofCrAnListF [φ, ψ]) * y - s • (x * ι (ofCrAnListF [ψ, φ])) * y)"
)
PH_ERROR = "\n".join([
    "candidate:79:21: error: unsolved goals",
    "𝓕 : FieldSpecification",
    "φ ψ : 𝓕.CrAnFieldOp",
    "hφψ : crAnTimeOrderRel φ ψ",
    "hψφ : crAnTimeOrderRel ψ φ",
    "a b : 𝓕.FieldOpFreeAlgebra",
    "F : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] 𝓕.WickAlgebra := ι.toLinearMap ∘ₗ timeOrderF",
    "C : 𝓕.FieldOpFreeAlgebra := (superCommuteF (ofCrAnOpF φ)) (ofCrAnOpF ψ)",
    "φs φs' : List 𝓕.CrAnFieldOp",
    "sorted : List 𝓕.CrAnFieldOp := List.insertionSort crAnTimeOrderRel (φs' ++ φs)",
    "before : List 𝓕.CrAnFieldOp := List.takeWhile (fun c => decide ¬crAnTimeOrderRel φ c) sorted",
    "tieLeft : List 𝓕.CrAnFieldOp := List.filter (fun c => decide (crAnTimeOrderRel φ c ∧ crAnTimeOrderRel c φ)) φs'",
    "tieRight : List 𝓕.CrAnFieldOp := List.filter (fun c => decide (crAnTimeOrderRel φ c ∧ crAnTimeOrderRel c φ)) φs",
    "after : List 𝓕.CrAnFieldOp := List.filter (fun c => decide (crAnTimeOrderRel φ c ∧ ¬crAnTimeOrderRel c φ)) sorted",
    "x : 𝓕.WickAlgebra := ι (ofCrAnListF before) * ι (ofCrAnListF tieLeft)",
    "y : 𝓕.WickAlgebra := ι (ofCrAnListF tieRight) * ι (ofCrAnListF after)",
    "s : ℂ := (exchangeSign (𝓕.crAnStatistics φ)) (𝓕.crAnStatistics ψ)",
    "t : ℂ := crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs)",
    PH_TARGET,
])


def assert_bounded(message):
    assert len(message) <= 1200
    assert len(message.splitlines()) <= 12


@pytest.mark.parametrize("error_type,status,valid", [
    (arena.LeanCompileError, "invalid", False),
    (arena.LeanTimeoutError, "timeout", None),
])
def test_ph_goal_and_wrapping_survive_without_changing_failure_evidence(error_type, status, valid):
    output = "\n " + PH_ERROR + "\n\n"
    assert "⊢" not in "\n".join(output.strip().splitlines()[:12])[:1200]
    run = arena.LeanRun(command=[], returncode=1, seconds=0.1, output=output,
                        timed_out=status == "timeout", log_path="/archive/full.log")
    error = error_type("candidate compilation failed", run)
    summary, details = {}, {}

    batches._failure(summary, details, error, phase="quick_primary")

    message = summary["diagnostic"]["message"]
    assert message.startswith("candidate:79:21: error: unsolved goals\n")
    assert PH_TARGET in message
    assert "t : ℂ := crAnTimeOrderSign" in message
    assert "[diagnostic text omitted]" in message
    assert summary["diagnostic"] == {"severity": "error", "message": message, "truncated": True}
    assert_bounded(message)
    assert summary["status"] == status and summary["valid"] is valid
    assert summary["score"] is None and summary["checkpoint"] is None
    assert summary["diagnostics_path"] == "/archive/full.log"
    assert details["lean_run"] == {"output": output, "log_path": "/archive/full.log",
                                   "returncode": 1, "timed_out": status == "timeout"}
    assert details["error"] == str(error) and run.output == output


@pytest.mark.parametrize("output", [
    "candidate:3:9: error: type mismatch\n  Nat.zero\nhas type\n  Nat\nbut is expected to have type\n  True",
    "candidate:3:9: error(lean.unknownIdentifier): Unknown identifier `missing`",
    "unsolved goals\ncase left\na : α\n⊢ first\n    wrapped\n\ncase right\nb : β\n⊢ second",
    "malformed text with an embedded ⊢ marker, no goal line",
])
def test_short_diagnostics_are_preserved_literally(output):
    summary = {}
    error = arena.LeanCompileError("compile failed", arena.LeanRun([], 1, 0.1, output))
    batches._failure_diagnostic(summary, error)
    assert summary["diagnostic"] == {"severity": "error", "message": output, "truncated": False}


def test_long_multiple_goals_keep_first_case_target_and_explicit_boundaries():
    output = "\n".join([
        "candidate:4:2: error: unsolved goals", "case left",
        *[f"left_{i} : α" for i in range(30)],
        "⊢ first_target", "    first_wrapped", "", "case right",
        "right_local : β", "⊢ second_target", "    second_wrapped", "",
        "candidate:9:3: error: unrelated error", "⊢ third_target",
    ])
    message = batches._failure_preview(output)
    assert message.startswith("candidate:4:2: error: unsolved goals\ncase left\n")
    assert "⊢ first_target\n    first_wrapped\n... [diagnostic text omitted]" in message
    assert "left_29 : α" in message
    assert not any(value in message for value in ("right_local", "second_", "third_", "unrelated error"))
    assert_bounded(message)


def test_later_diagnostic_goal_keeps_its_own_header_and_context():
    output = "\n".join([
        "candidate:2:1: error: type mismatch", *[f"first error detail {i}" for i in range(30)],
        "  candidate:8:4: error: unsolved goals", "wrong_local : α", "⊢ later_target",
    ])
    message = batches._failure_preview(output)
    assert message.startswith("candidate:2:1: error: type mismatch\n... [diagnostic text omitted]\n")
    assert "[diagnostic text omitted]" in message
    assert "  candidate:8:4: error: unsolved goals\nwrong_local : α\n⊢ later_target" in message
    assert message.index("[diagnostic text omitted]") < message.index("candidate:8:4:")
    assert_bounded(message)


def test_warning_example_does_not_replace_an_error_with_no_goal():
    output = "\n".join([
        "candidate:2:1: error: type mismatch", *[f"error detail {i}" for i in range(30)],
        "candidate:8:4: warning: illustrative tactic state", "⊢ warning_example",
    ])
    message = batches._failure_preview(output)
    assert message.startswith("candidate:2:1: error: type mismatch\nerror detail 0")
    assert "warning_example" not in message
    assert_bounded(message)


@pytest.mark.parametrize("target", ["⊢ " + "😀λ" * 5000, "⊢ first\n" + "    wrapped\n" * 50])
def test_oversized_targets_are_bounded_and_visibly_incomplete(target):
    output = "candidate:7:2: error: unsolved goals\n" + "local : α\n" * 50 + target
    message = batches._failure_preview(output)
    assert message.startswith("candidate:7:2: error: unsolved goals\n")
    assert "⊢ " in message and "[diagnostic text omitted]" in message
    assert_bounded(message)
    assert message == batches._failure_preview(output)


def test_malformed_long_text_and_unusually_long_header_remain_bounded():
    malformed = "raw compiler text ⊢ " + "?" * 2000
    message = batches._failure_preview(malformed)
    assert message.startswith("raw compiler text ⊢ ")
    assert message.endswith("[diagnostic text omitted]")
    assert_bounded(message)
    output = "candidate:1:1: error: " + "long header " * 200 + "\ncase " + "huge " * 200 + "\n⊢ small_target"
    message = batches._failure_preview(output)
    assert message.startswith("candidate:1:1: error:") and "⊢ small_target" in message
    assert_bounded(message)


def test_empty_output_uses_exception_summary_without_a_preview_failure():
    summary = {}
    batches._failure_diagnostic(summary, arena.LeanCompileError("compile failed", arena.LeanRun([], 1, 0.1, "")))
    assert summary["diagnostic"]["message"] == "compile failed"

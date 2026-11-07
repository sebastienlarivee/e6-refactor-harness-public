"""Synthetic assignment and compatibility harness regressions; no Lean calls."""
from pathlib import Path

import pytest

from lean_tools import lean_source
from lean_tools.workflow_errors import WorkflowError


PROOF_BODIES = (
    "by\n  trivial",
    "set_option simprocs false in by\n  trivial",
    "set_option simprocs false in\n"
    "  set_option smartUnfolding false in by\n    trivial",
    "by\n  set_option simprocs false in\n    trivial",
    "True.intro",
)
NESTED_SIGNATURE = (
    "theorem demo (n : Nat := by exact (let value := 0; value))\n"
    '    (label : String := ":= by ( let have") :\n'
    "  /- := by /- nested := by -/ -/\n"
    "  let «P := by» : Prop := True\n"
    "  let h : «P := by» := by trivial\n"
    "  «P := by»"
)


@pytest.mark.parametrize("body", PROOF_BODIES)
@pytest.mark.parametrize(
    "signature",
    (
        "theorem demo : True",
        NESTED_SIGNATURE,
        "theorem demo : let P := let Q := True; Q; P",
        "theorem demo : have h : True := by trivial; True",
        "theorem demo : let rec f : Nat → Nat | 0 => 0 | n+1 => f n; True",
    ),
)
def test_assignment_ignores_body_shape_and_statement_assignments(
    signature: str, body: str
) -> None:
    separator = "\n/- := by /- nested -/ -/ -- := by\n := "
    source = signature + separator + body
    expected = len(signature) + separator.rindex(":=")

    assert lean_source.declaration_assignment_start(
        source, "demo", signature=signature
    ) == expected
    assert lean_source.exact_signature_assignment_start(source, signature) == expected


@pytest.mark.parametrize("body", PROOF_BODIES[:-1])
def test_supplied_assignment_fallback_preserves_normalized_signature(body: str) -> None:
    signature = "theorem demo (a b : Nat) : True"
    original_signature = "theorem demo (a : Nat) (b : Nat) : True"
    original = original_signature + " := " + body
    row = {"name": "demo", "signature": signature, "src": original}

    assert lean_source.supplied_assignment_start(row) == len(original_signature) + 1
    assert lean_source.validate_supplied_declaration(row, original) == body
    canonical = lean_source.canonical_candidate_declaration(row)
    assert canonical == signature + " := " + body
    assert lean_source.validate_declaration(row, canonical) == body


def test_supplied_normalization_fallback_retains_equation_style_type() -> None:
    statement = "let rec f : Nat → Nat | 0 => 0 | n+1 => f n; True"
    signature = "theorem demo (a b : Nat) : " + statement
    original_signature = "theorem demo (a : Nat) (b : Nat) : " + statement
    original = original_signature + " := by trivial"
    row = {"name": "demo", "signature": signature, "src": original}

    assert lean_source.supplied_assignment_start(row) == len(original_signature) + 1
    assert lean_source.canonical_candidate_declaration(row) == signature + " := by trivial"


@pytest.mark.parametrize("body", PROOF_BODIES)
@pytest.mark.parametrize("source_body", PROOF_BODIES[:3])
@pytest.mark.parametrize("structural", (False, True))
@pytest.mark.parametrize("measured", (False, True))
def test_project_harness_accepts_option_bodies_in_both_source_paths(
    tmp_path: Path,
    body: str,
    source_body: str,
    structural: bool,
    measured: bool,
) -> None:
    original = NESTED_SIGNATURE + " := " + source_body
    row = {
        "name": "Outer.demo",
        "signature": NESTED_SIGNATURE,
        "src": original,
        "file_path": "Demo.lean",
    }
    source_signature = (
        NESTED_SIGNATURE.replace("theorem demo", "theorem  demo", 1)
        if structural else NESTED_SIGNATURE
    )
    prefix = "import Mathlib\n\nnamespace Outer\n\ndef before := 7\n\n"
    source = (
        prefix + source_signature + " := " + source_body
        + "\n\nlemma later : True := by trivial\nend Outer\n"
    )
    (tmp_path / "Demo.lean").write_text(source, encoding="utf-8")
    assert (source.count(original) == 0) == structural
    candidate = NESTED_SIGNATURE + " := " + body
    assert lean_source.validate_declaration(row, candidate) == body

    harness = lean_source.project_compile_harness(
        row, candidate, tmp_path, exact=measured
    )

    assert harness.endswith(candidate + "\n")
    assert harness.count(candidate) == 1
    assert "def before := 7" in harness
    assert "lemma later" not in harness
    if measured:
        assert harness.startswith("import LrhMeasurement\n" + prefix)
        assert "set_option Elab.async false in\nlrh_measured_decl " in harness
    else:
        assert harness == prefix + candidate + "\n"


@pytest.mark.parametrize("body", PROOF_BODIES[:3])
@pytest.mark.parametrize("measured", (False, True))
@pytest.mark.parametrize(
    ("signature", "changed_signature"),
    (
        ("theorem demo : True", "theorem demo : False"),
        (
            "theorem demo : let P := True; P",
            "theorem demo : let P := True; False",
        ),
        (
            "theorem demo (n : Nat := by exact 0) : True",
            "theorem demo (n : Nat := by exact 1) : True",
        ),
    ),
)
def test_project_harness_keeps_statement_frozen_with_option_bodies(
    tmp_path: Path,
    signature: str,
    changed_signature: str,
    body: str,
    measured: bool,
) -> None:
    row = {
        "name": "demo",
        "signature": signature,
        "src": signature + " := by trivial",
        "file_path": "Demo.lean",
    }
    (tmp_path / "Demo.lean").write_text(
        "import Mathlib\n\n" + changed_signature + " := " + body + "\n",
        encoding="utf-8",
    )

    with pytest.raises(WorkflowError, match="theorem statement changed"):
        lean_source.project_compile_harness(
            row, signature + " := " + body, tmp_path, exact=measured
        )


def test_assignment_missing_outside_binders_and_comments() -> None:
    with pytest.raises(WorkflowError, match="declaration-level ':='"):
        lean_source.declaration_assignment_start(
            "theorem demo (n : Nat := by exact 0) : True /- := by trivial -/",
            "demo",
        )

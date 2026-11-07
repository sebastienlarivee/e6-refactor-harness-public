"""Current-source byte mapping, continuation edits and native helper contracts."""
from __future__ import annotations

import json
from pathlib import Path
import time

import pytest

from e6 import deterministic_native as native
from e6.experiment import DEFAULT_SPEC
from lean_tools import lean_source


def _span(source, text):
    first = source.index(text)
    return {"start_byte": len(source[:first].encode()), "end_byte": len(source[:first + len(text)].encode())}


def _sequence(source, texts):
    children = [_span(source, text) | {"kind": "Synthetic.tactic"} for text in texts]
    return {"start_byte": children[0]["start_byte"], "end_byte": children[-1]["end_byte"],
            "children": children, "kind": "Lean.Parser.Tactic.tacticSeq1Indented"}


def _scan(source, texts):
    return {"proof_start_byte": len(source[:source.index("by")].encode()),
            "declaration_end_byte": len(source.encode()), "sequences": [_sequence(source, texts)], "terms": []}


def _task(tmp_path):
    row = {"name": "Fixture.target", "header": "import Lean\nnamespace Fixture\n", "contexts": [],
           "signature": "theorem target (p : Prop) (h : p) : p",
           "src": "theorem target (p : Prop) (h : p) : p := by\n  skip\n  exact h"}
    path = tmp_path / "Task.json"
    path.write_text(json.dumps({"schema_version": 1, "row": row}))
    return row, {**DEFAULT_SPEC.proof_settings(), "task": str(path),
                 "primary": str(tmp_path / "cached-project"), "root": str(tmp_path)}


def test_utf8_child_window_retains_entire_suffix():
    source = "theorem target (α : Prop) (h : α) : α := by\n  skip\n  have h' := h\n  exact h'\n"
    scan = _scan(source, ["skip", "have h' := h", "exact h'"])
    proposals = native.proposals_from_inventory(source, scan)
    one = next(item for item in proposals if item["family"] == "native-delete" and item["old"].startswith("skip"))
    assert one["source"] == source.replace("  skip\n", "", 1)
    two = next(item for item in proposals if item["family"] == "native-delete-window" and item["width"] == 2)
    assert "exact h'\n" in two["source"]
    assert two["source"].startswith(source[:source.index("by")])
    assert two["validation_required"] == "complete_source_exact_axioms_and_compatibility"


def test_deletion_consumes_inline_semicolon_separator():
    source = "theorem target : True := by skip; exact True.intro"
    proposals = native.proposals_from_inventory(source, _scan(source, ["skip", "exact True.intro"]))
    assert any(item["source"] == "theorem target : True := by exact True.intro" for item in proposals)


def test_rule_subsets_keep_nested_terms_and_location_suffix():
    proposals = native._rule_subsets("simp only [foo (a, b), ← bar, baz [x, y]] at h ⊢")
    assert len(proposals) >= 4
    assert any(item["replacement"] == "simp only [← bar, baz [x, y]] at h ⊢" for item in proposals)
    assert any(item["replacement"] == "simp only [] at h ⊢" for item in proposals)
    assert native._rule_subsets("exact f [a, b]") == []


def test_native_wrapper_is_unindented_with_following_continuation():
    wrapper = "focus\n    skip\n    exact h"
    source = "theorem target (p : Prop) (h : p) : p := by\n  " + wrapper + "\n  done"
    outer = _sequence(source, [wrapper, "done"])
    inner = _sequence(source, ["skip", "exact h"])
    scan = {"proof_start_byte": source.index("by"), "sequences": [outer, inner], "terms": []}
    proposals = native.proposals_from_inventory(source, scan)
    candidate = next(item for item in proposals if item["family"] == "native-delete-wrapper")
    assert "by\n  skip\n  exact h\n  done" in candidate["source"]


def test_term_hints_include_inferred_and_whnf_and_unicode_hidden_argument():
    old = "id n"
    record = {"start_byte": 0, "end_byte": len(old), "head_end_byte": 2,
              "kind": "Lean.Parser.Term.app", "normal": old, "explicit": "@id Alias n",
              "type": "Alias", "whnf_type": "Nat", "head_constant": "id",
              "application": [{"name": "α", "explicit": False, "instance": False, "index": 0,
                               "value": "Alias", "type": "Type", "whnf_type_value": "Nat"},
                              {"name": "a", "explicit": True, "index": 1, "value": "n"}]}
    proposals = native._term_replacements(old, record)
    assert ("inferred-type", "(id n : Alias)", {"type": "Alias"}) in proposals
    assert ("normalized-type", "(id n : Nat)", {"type": "Nat"}) in proposals
    assert any(family == "named-implicit" and text == "id (α := Alias) n" for family, text, _ in proposals)
    assert any(family == "normalized-type-argument" and text == "id (α := Nat) n" for family, text, _ in proposals)


def test_term_replacements_require_consensus_between_observed_contexts():
    source = "theorem target (p : Prop) (h : p) : p := by exact id h"
    span = _span(source, "id h")
    common = {**span, "kind": "Lean.Parser.Term.app", "normal": "id h", "explicit": "", "type": "", "whnf_type": ""}
    scan = _scan(source, ["exact id h"])
    scan["terms"] = [common | {"type": "p"}, common | {"type": "q"}]
    proposals = native.proposals_from_inventory(source, scan)
    assert not any(item["family"] == "inferred-type" for item in proposals)


def test_zero_or_tiny_budget_is_bounded_and_sources_deduplicate():
    source = "theorem target : True := by skip; skip; exact True.intro"
    scan = _scan(source, ["skip", "exact True.intro"])
    assert native.proposals_from_inventory(source, scan, max_candidates=0) == []
    proposals = native.proposals_from_inventory(source, scan, max_candidates=1)
    assert len(proposals) == 1
    assert len({item["source_sha256"] for item in proposals}) == len(proposals)


def test_generate_uses_current_source_not_original_and_records_inventory(tmp_path, monkeypatch):
    row, config = _task(tmp_path)
    original = lean_source.render_candidate_scaffold(row)
    current = original.replace("skip", "have h2 := h")
    observed = []
    def inventory(config_arg, source, row_arg, workdir, deadline):
        observed.append(source)
        assert workdir.is_relative_to(tmp_path / "boundary")
        return _scan(source, ["have h2 := h", "exact h"]), {"helper_build": {"reused": True}}
    monkeypatch.setattr(native, "_inventory", inventory)
    monkeypatch.setattr(native, "configure_native_environment", lambda **_: {})
    proposals = native.generate(config, current, tmp_path / "boundary", max_candidates=2)
    assert observed == [current]
    assert proposals
    receipt = json.loads((tmp_path / "boundary/native-proposals.json").read_text())
    assert receipt["status"] == "completed"
    assert receipt["source_sha256"] == native._sha(current)
    assert receipt["model_calls"] == 0


def test_helper_failure_is_raised_with_persisted_failure_receipt(tmp_path, monkeypatch):
    row, config = _task(tmp_path)
    monkeypatch.setattr(native, "configure_native_environment", lambda **_: {})
    def broken(*args):
        raise RuntimeError("compiler API differs")
    monkeypatch.setattr(native, "_inventory", broken)
    with pytest.raises(native.NativeProposalError, match="compiler API differs"):
        native.generate(config, lean_source.render_candidate_scaffold(row), tmp_path / "boundary")
    receipt = json.loads((tmp_path / "boundary/native-proposals.json").read_text())
    assert receipt["status"] == "failed"
    assert receipt["error_type"] == "RuntimeError"
    assert "compiler API differs" in receipt["error"]


def test_invalid_signature_never_launches(tmp_path, monkeypatch):
    row, config = _task(tmp_path)
    monkeypatch.setattr(native, "_inventory", lambda *args: pytest.fail("must reject before native launch"))
    source = lean_source.render_candidate_scaffold(row).replace("(h : p)", "(h : True)")
    with pytest.raises(native.NativeProposalError, match="exact signature"):
        native.generate(config, source, tmp_path / "boundary")


def test_helper_cache_reuses_only_matching_compiler_environment_and_helper(tmp_path, monkeypatch):
    project = tmp_path / "project"
    project.mkdir()
    config = {"root": str(tmp_path / "run")}
    guard = {"toolchain": "synthetic-v1", "githash": "abcdef"}
    monkeypatch.setattr(native.lean_launch, "workspace_guard", lambda *_: guard)
    calls = []
    def run(path, project_arg, deadline, log, **kwargs):
        calls.append(path)
        Path(kwargs["lean_args"][-1]).write_bytes(b"compiled helper")
        return {"returncode": 0, "timed_out": False}
    monkeypatch.setattr(native, "_run", run)
    deadline = time.perf_counter() + 30
    first, receipt, _ = native._helper(config, project, tmp_path, False, deadline)
    second, reused, _ = native._helper(config, project, tmp_path, False, deadline)
    assert first == second and reused["reused"] is True and len(calls) == 1
    guard["githash"] = "changed"
    third, _, _ = native._helper(config, project, tmp_path, False, deadline)
    assert third != first and len(calls) == 2


def test_helper_cache_cannot_write_to_cached_project(tmp_path, monkeypatch):
    guard = {"toolchain": "synthetic"}
    monkeypatch.setattr(native.lean_launch, "workspace_guard", lambda *_: guard)
    with pytest.raises(native.NativeProposalError, match="outside"):
        native._helper({"root": str(tmp_path)}, tmp_path, tmp_path, False, time.perf_counter() + 30)


def test_project_inventory_uses_exact_original_prefix_and_maps_current_utf8_source(tmp_path, monkeypatch):
    row, config = _task(tmp_path)
    project = Path(config["primary"])
    project.mkdir()
    row["file_path"] = "Fixture.lean"
    project_source = ("import Lean\nnamespace Fixture\n" + row["src"]
                      + "\ntheorem later : True := by trivial\n")
    (project / "Fixture.lean").write_text(project_source)
    current_declaration = row["src"].replace("skip", "have α := h")
    source = lean_source.render_candidate_scaffold(row).replace(row["src"], current_declaration)
    output = tmp_path / "private-inventory"
    output.mkdir()
    monkeypatch.setattr(native, "_helper", lambda *args: (tmp_path / "helper", {"reused": True}, {"compiler": "test"}))
    def run(path, project_arg, deadline, log, **kwargs):
        harness = path.read_text()
        assert "theorem later" not in harness
        assert harness.count("theorem target") == 1
        assert current_declaration in harness
        assert harness.startswith("import Lean\nimport E6NativeInventoryHelper\n")
        command = next(line for line in harness.splitlines() if line.startswith("#e6_native_inventory "))
        raw_path = Path(json.JSONDecoder().raw_decode(command[len("#e6_native_inventory "):])[0])
        offset = len(harness[:harness.index(current_declaration)].encode())
        record = _span(harness, "have α := h")
        scan = {"schema_version": 1, "native_environment_target_present": False,
                "proof_start_byte": offset + len(row["signature"].encode()),
                "sequences": [{**record, "children": [record.copy()]}], "terms": []}
        raw_path.write_text(json.dumps(scan))
        return {"returncode": 0, "timed_out": False}
    monkeypatch.setattr(native, "_run", run)
    scan, _ = native._inventory(config, source, row, output, time.perf_counter() + 30)
    assert scan["sequences"][0]["children"][0] == _span(source, "have α := h")
    assert scan["declaration_end_byte"] == len(source[:source.index(lean_source.TARGET_END)].rstrip("\n").encode())


def test_source_identical_compile_failure_is_cached(tmp_path, monkeypatch):
    project = tmp_path / "project"
    project.mkdir()
    monkeypatch.setattr(native.lean_launch, "workspace_guard", lambda *_: {"toolchain": "synthetic"})
    calls = []
    def broken(path, project_arg, deadline, log, **kwargs):
        calls.append(path)
        log.write_text("error: unsupported compiler API")
        return {"returncode": 1, "timed_out": False}
    monkeypatch.setattr(native, "_run", broken)
    for _ in range(2):
        with pytest.raises(native.NativeProposalError, match="compile fail"):
            native._helper({"root": str(tmp_path)}, project, tmp_path, False, time.perf_counter() + 30)
    assert len(calls) == 1


@pytest.mark.parametrize("kwargs", [{"timeout_seconds": True}, {"timeout_seconds": 0},
                                     {"timeout_seconds": float("nan")}, {"max_candidates": True}])
def test_invalid_budgets_are_rejected(tmp_path, kwargs):
    with pytest.raises(ValueError):
        native.generate({"primary": str(tmp_path / "project")}, "theorem target : True := by trivial", tmp_path, **kwargs)


def _regional(source, texts, terms=()):
    scan = _scan(source, texts)
    scan["terms"] = list(terms)
    return [item for item in native.proposals_from_inventory(source, scan, regional=True)
            if item["family"].startswith("native-regional-")]


def test_regional_is_opt_in_and_replaces_blind_windows():
    source = "theorem target (p : Prop) (h : p) : p := by\n  have unused := h\n  exact h\n"
    scan = _scan(source, ["have unused := h", "exact h"])
    base = native.proposals_from_inventory(source, scan)
    regional = native.proposals_from_inventory(source, scan, regional=True)
    assert not any(item["family"].startswith("native-regional-") for item in base)
    assert any(item["family"] == "native-delete-window" for item in base)
    assert not any("delete-window" in item["family"] for item in regional)
    unused = next(item for item in regional if item["family"] == "native-regional-unused-local")
    assert unused["source"] == source.replace("  have unused := h\n", "")
    assert unused["dependency_evidence"] == "conservative_lexical_suffix"
    assert unused["candidate_validity"] == "requires_full_source_validation"


def test_regional_local_dependency_closure_prunes_only_unused_suffix():
    source = "theorem target (p : Prop) (h : p) : p := by\n  have α := h\n  have β := id α\n  exact h\n"
    proposals = _regional(source, ["have α := h", "have β := id α", "exact h"])
    pair = next(item for item in proposals if item["family"] == "native-regional-prune")
    assert pair["source"] == "theorem target (p : Prop) (h : p) : p := by\n  exact h\n"
    assert pair["removed_local_names"] == ["α", "β"]
    assert not any(item["removed_local_names"] == ["α"] for item in proposals)
    used = source.replace("exact h", "exact β")
    assert _regional(used, ["have α := h", "have β := id α", "exact β"]) == []


def test_native_hidden_dependency_blocks_lexically_unused_local():
    source = "theorem target : True := by\n  have localFact := True.intro\n  exact f\n"
    term = _span(source, "f\n")
    term["end_byte"] -= 1
    # Native TermInfo supplies the dependency introduced by elaboration, even
    # though the explicit source term does not mention localFact.
    term = {**term, "free_variables": ["localFact"], "type_free_variables": [],
            "kind": "Lean.Parser.Term.ident", "normal": "f"}
    assert _regional(source, ["have localFact := True.intro", "exact f"], [term]) == []


@pytest.mark.parametrize("suffix", ["simp_all", "assumption", "aesop", "all_goals exact h",
                                     "first | exact h", "exact (by trivial)", "simp only [] at *",
                                     "exact h.property", "exact «opaque»"])
def test_regional_abstains_on_opaque_or_referenced_continuations(suffix):
    source = "theorem target : True := by\n  have h := True.intro\n  " + suffix
    assert _regional(source, ["have h := True.intro", suffix]) == []


def test_regional_never_analyzes_nested_suffix_without_outer_continuation():
    wrapper = "focus\n    have x := h\n    skip"
    source = "theorem target (p : Prop) (h : p) : p := by\n  " + wrapper + "\n  exact x"
    scan = _scan(source, [wrapper, "exact x"])
    scan["sequences"].append(_sequence(source, ["have x := h", "skip"]))
    proposals = native.proposals_from_inventory(source, scan, regional=True)
    assert not any(item["family"].startswith("native-regional-") for item in proposals)


def test_regional_clear_continuation_repair_preserves_complete_source():
    source = "theorem target (p : Prop) (h : p) : p := by\n  have unused := h\n  clear unused\n  exact h\n"
    proposals = _regional(source, ["have unused := h", "clear unused", "exact h"])
    repair = next(item for item in proposals if item["family"] == "native-regional-repair")
    assert repair["source"] == "theorem target (p : Prop) (h : p) : p := by\n  exact h\n"
    assert repair["continuation_repairs"][0]["repair"] == "clear_local_prune"
    assert repair["retains_complete_continuation"] is True


def test_regional_clear_repair_keeps_other_named_locals_and_inline_separator():
    source = "theorem target (p : Prop) (h : p) : p := by have x := h; clear x y; exact h"
    proposals = _regional(source, ["have x := h", "clear x y", "exact h"])
    repair = next(item for item in proposals if item["family"] == "native-regional-repair")
    assert repair["source"] == "theorem target (p : Prop) (h : p) : p := by clear y; exact h"


def test_regional_local_rule_repair_preserves_using_and_location():
    source = "theorem target (p : Prop) (h : p) : p := by\n  have hlocal := h\n  simpa only [hlocal, globalRule] using h\n"
    proposals = _regional(source, ["have hlocal := h", "simpa only [hlocal, globalRule] using h"])
    repair = next(item for item in proposals if item["family"] == "native-regional-repair")
    assert repair["source"].endswith("by\n  simpa only [globalRule] using h\n")
    assert native._drop_local_rules("simp only [hlocal] at hlocal", {"hlocal"}) is None
    assert native._drop_local_rules("simp only [foo hlocal]", {"hlocal"}) is None
    assert native._drop_local_rules("simp only [hlocal, hlocal.property]", {"hlocal"}) is None


def test_regional_repair_budget_excludes_long_or_broad_continuations():
    source = "theorem target : True := by\n  have x := True.intro\n  clear x\n" + "  skip\n" * 8 + "  exact True.intro"
    # Build duplicate skip spans explicitly, rather than the helper's first-match
    # convenience, to keep this a real nine-child continuation.
    scan = _scan(source, ["have x := True.intro", "clear x", "exact True.intro"])
    start = source.index("  skip")
    skips = []
    for offset in range(8):
        a = start + offset * len("  skip\n") + 2
        skips.append({"start_byte": a, "end_byte": a + 4, "kind": "Synthetic.tactic"})
    scan["sequences"][0]["children"][2:2] = skips
    proposals = native.proposals_from_inventory(source, scan, regional=True)
    assert not any(item["family"] == "native-regional-repair" for item in proposals)


def test_regional_normalization_delay_uses_native_dependencies_and_keeps_suffix():
    source = "theorem target (p : Prop) (h q : p) : p := by\n  rw [rule] at h\n  have witness := q\n  exact h\n"
    texts = ["rw [rule] at h", "have witness := q", "exact h"]
    proposals = _regional(source, texts)
    delay = next(item for item in proposals if item["family"] == "native-regional-normalization-delay")
    assert delay["source"].endswith("by\n  have witness := q\n  rw [rule] at h\n  exact h\n")
    term = {**_span(source, "q\n"), "free_variables": ["h"], "type_free_variables": []}
    term["end_byte"] -= 1
    assert not any(item["family"] == "native-regional-normalization-delay"
                   for item in _regional(source, texts, [term]))


@pytest.mark.parametrize("body", ["repeat apply f", "all_goals repeat apply f",
                                  "repeat' apply f", "repeat (apply f)"])
def test_native_deletion_cannot_create_direct_repeat_skip(body):
    source = "theorem target : True := by\n  " + body + "\n  exact True.intro"
    scan = _scan(source, [body, "exact True.intro"])
    scan["sequences"].append(_sequence(source, ["apply f"]))
    proposals = native.proposals_from_inventory(source, scan)
    assert not any(native._obvious_nonprogress_repeat(item["source"]) for item in proposals)
    assert any(item["family"] == "native-delete" and item["old"].startswith(body)
               for item in proposals)


@pytest.mark.parametrize("branch", ["assumption", "apply List.nil_sublist", "apply List.Sublist.refl"])
def test_native_deletion_cannot_create_skip_in_repeat_first_branch(branch):
    body = "repeat' first\n    | assumption\n    | apply List.nil_sublist\n    | apply List.Sublist.refl"
    source = "theorem target : True := by\n  " + body
    scan = _scan(source, [body])
    scan["sequences"].append(_sequence(source, [branch]))
    proposals = native.proposals_from_inventory(source, scan)
    assert not any(item["start_byte"] == _span(source, branch)["start_byte"]
                   and item["replacement"] == "skip" for item in proposals)


@pytest.mark.parametrize("text", ["repeat skip", "repeat' (skip)",
                                  "repeat' first | skip | exact h",
                                  "repeat (first | assumption | skip)",
                                  "all_goals repeat (repeat' skip)",
                                  "repeat' first\n  | assumption\n  | (skip)\nexact h"])
def test_nonprogress_repeat_guard_recognizes_nested_and_layout_shapes(text):
    assert native._obvious_nonprogress_repeat(text)


@pytest.mark.parametrize("text", ["repeat (skip; apply h)", "repeat' first | skip; apply h | assumption",
                                  "repeat apply f\nfirst | skip | exact h",
                                  "repeat' first\n  | first\n      | skip\n      | fail\n    apply h\n  | assumption",
                                  "exact \"repeat skip\"", "repeat apply f -- repeat skip"])
def test_nonprogress_repeat_guard_keeps_progress_and_unrelated_first(text):
    assert not native._obvious_nonprogress_repeat(text)


def test_regional_filters_target_bounds_before_both_sequence_quotas():
    prefix = "theorem signatureProof : True := by trivial\n" * 520
    source = prefix + "theorem target (h : True) : True := by\n  have unused := h\n  exact h"
    scan = _scan(source, ["have unused := h", "exact h"])
    scan["proof_start_byte"] = len(source[:source.rindex("by")].encode())
    for i in range(520):
        a = i * len("theorem signatureProof : True := by trivial\n") + len("theorem signatureProof : True := by ")
        scan["sequences"].append({"start_byte": a, "end_byte": a + 7,
                                  "children": [{"start_byte": a, "end_byte": a + 7}]})
    proposals = native.proposals_from_inventory(source, scan, regional=True)
    assert any(item["family"] == "native-regional-unused-local" for item in proposals)
    assert all(item["start_byte"] >= scan["proof_start_byte"] for item in proposals)


def test_parameterized_local_binding_is_narrow_and_top_level():
    assert native._local_binding(native.lex("have hq k := f k")) == "hq"
    assert native._local_binding(native.lex("have hEd j k : P j k := f j k")) == "hEd"
    for text in ["have ⟨a, b⟩ := h", "have h (k : Nat) := f k", "haveI h := f",
                 "letI h := f", "have h : P (x := y)"]:
        assert native._local_binding(native.lex(text)) is None


@pytest.mark.parametrize("text,expected", [
    ("simp -dsimp only [←hq, hf]", "simp -dsimp only [hf]"),
    ("simp +singlePass -dsimp only [hf, hq]", "simp +singlePass -dsimp only [hf]"),
    ("simp (maxDischargeDepth := 3) only [hq, hf] at h", "simp (maxDischargeDepth := 3) only [hf] at h"),
    ("rw [←hq, hf]", "rw [hf]"),
])
def test_local_rule_repair_preserves_native_simp_modifiers(text, expected):
    assert native._drop_local_rules(text, {"hq"}) == expected


def test_opaque_regional_repair_removes_local_and_repairs_its_normalization_uses():
    source = ("theorem target : True := by\n"
              "  have hq k := f k\n"
              "  simp -dsimp only [rule] at hq hf\n"
              "  simp only [←hq, hf]\n"
              "  ring1\n")
    texts = ["have hq k := f k", "simp -dsimp only [rule] at hq hf", "simp only [←hq, hf]", "ring1"]
    proposals = _regional(source, texts)
    repair = next(item for item in proposals if item["family"] == "native-regional-opaque-repair")
    assert repair["source"] == ("theorem target : True := by\n"
                                "  simp -dsimp only [rule] at hf\n  simp only [hf]\n  ring1\n")
    assert repair["opaque_trial"] is True
    assert repair["native_dependency_certified"] is False
    assert repair["dependency_evidence"] == "bounded_explicit_reference_repairs_only"
    assert len(repair["continuation_repairs"]) == 2
    assert not any(item["family"] == "native-regional-unused-local" for item in proposals)


def test_opaque_repair_prunes_only_removed_local_normalization_and_keeps_goal_location():
    texts = ["have hg := f", "unfold Space.div at hg", "simp only [rule] at hg ⊢",
             "simp only [hg, globalRule]", "aesop"]
    source = "theorem target : True := by\n  " + "\n  ".join(texts)
    repair = next(item for item in _regional(source, texts)
                  if item["family"] == "native-regional-opaque-repair")
    assert repair["source"].endswith("by\n  simp only [rule] at ⊢\n  simp only [globalRule]\n  aesop")
    assert repair["continuation_repairs"][0]["repair"] == "deleted_local_normalization_prune"


def test_opaque_repair_requires_actual_followup_repair_and_blocks_unrepairable_native_use():
    texts = ["have x := f", "clear x", "simp_all"]
    source = "theorem target : True := by\n  " + "\n  ".join(texts)
    assert any(item["family"] == "native-regional-opaque-repair" for item in _regional(source, texts))
    native_use = {**_span(source, "simp_all"), "free_variables": ["x"], "type_free_variables": []}
    assert not any(item["family"] == "native-regional-opaque-repair"
                   for item in _regional(source, texts, [native_use]))
    assert _regional(source.replace("  clear x\n", ""), [texts[0], texts[-1]]) == []


def test_opaque_normalization_delay_swaps_only_disjoint_locations_and_keeps_suffix():
    texts = ["rw [Time.deriv_eq]", "unfold Space.div at hg", "simp_all"]
    source = "theorem target : True := by\n  " + "\n  ".join(texts)
    moved = next(item for item in _regional(source, texts)
                 if item["family"] == "native-regional-opaque-normalization-delay")
    assert moved["source"].endswith("by\n  unfold Space.div at hg\n  rw [Time.deriv_eq]\n  simp_all")
    assert moved["opaque_trial"] and moved["native_dependency_certified"] is False
    conflicting = source.replace("rw [Time.deriv_eq]", "rw [hg]")
    assert not any(item["family"] == "native-regional-opaque-normalization-delay"
                   for item in _regional(conflicting, ["rw [hg]", *texts[1:]]))


def test_opaque_normalization_delay_across_local_by_proof_is_only_a_trial():
    texts = ["rw [rule] at h", "have witness : True := by trivial", "exact h"]
    source = "theorem target : True := by\n  " + "\n  ".join(texts)
    moved = next(item for item in _regional(source, texts)
                 if item["family"] == "native-regional-opaque-normalization-delay")
    assert moved["source"].endswith("by\n  have witness : True := by trivial\n  rw [rule] at h\n  exact h")
    assert moved["dependency_evidence"] == "bounded_explicit_reference_screen_only"


@pytest.mark.parametrize("printed", ["@id _ n", "f ?_", "f (_ : Nat)", "Type _", "f ⋯"])
def test_printed_placeholders_are_rejected_before_exact_evaluation(printed):
    assert not native._replay_text(printed)
    old = "id n"
    record = {"start_byte": 0, "head_end_byte": 2, "kind": "Lean.Parser.Term.app",
              "normal": printed, "explicit": printed, "type": printed, "whnf_type": printed}
    assert native._term_replacements(old, record) == []
    assert native._replay_text("proof_with_underscores n")


def test_named_instance_requires_matching_surface_head_but_valid_instances_remain():
    old = "field n"
    argument = {"name": "self", "name_is_accessible": True, "instance": True,
                "explicit": False, "index": 0, "value": "instFoo"}
    record = {"start_byte": 0, "head_end_byte": 5, "kind": "Lean.Parser.Term.app",
              "normal": old, "explicit": "@Foo.field instFoo n", "head_constant": "Foo.field",
              "application": [argument], "surface_head_matches": False}
    proposals = native._term_replacements(old, record)
    assert not any(family == "named-instance" for family, _, _ in proposals)
    assert any(family == "native-explicit" for family, _, _ in proposals)
    valid = native._term_replacements(old, record | {"surface_head_matches": True})
    assert any(family == "named-instance" and text == "field (self := instFoo) n"
               for family, text, _ in valid)
    inaccessible = native._term_replacements(old, record | {"surface_head_matches": True,
        "application": [argument | {"name_is_accessible": False}]})
    assert not any(family == "named-instance" for family, _, _ in inaccessible)


def test_selective_holes_require_inference_evidence_for_every_omitted_parameter():
    old = "f n"
    args = [{"name": "α", "explicit": False, "index": 0, "value": "Nat"},
            {"name": "inst", "explicit": False, "instance": True, "index": 1, "value": "instFoo"},
            {"name": "n", "explicit": True, "index": 2, "value": "n"}]
    record = {"start_byte": 0, "head_end_byte": 1, "kind": "Lean.Parser.Term.app",
              "normal": old, "head_constant": "f", "application": args}
    assert not any(family.startswith("selective-") for family, _, _ in native._term_replacements(old, record))
    args[0]["inferable_from_explicit"] = True
    proposals = native._term_replacements(old, record)
    assert any(family == "selective-instance" and text == "(@f _ instFoo n)"
               for family, text, _ in proposals)
    assert not any(family == "selective-implicit" for family, _, _ in proposals)


def test_fresh_native_head_records_control_surface_binder_emission():
    source = "theorem target (n : Nat) : Nat := by exact id n"
    scan = _scan(source, ["exact id n"])
    application = {**_span(source, "id n"), "head_end_byte": _span(source, "id")["end_byte"],
                   "kind": "Lean.Parser.Term.app", "head_constant": "id", "is_constant": False,
                   "application": [{"name": "α", "explicit": False, "index": 0, "value": "Nat"}]}
    head = {**_span(source, "id"), "is_constant": True, "constant_name": "id"}
    scan["terms"] = [application, head]
    assert any(item["family"] == "named-implicit" for item in native.proposals_from_inventory(source, scan))
    head["constant_name"] = "Coee.coe"
    assert not any(item["family"] == "named-implicit" for item in native.proposals_from_inventory(source, scan))


def test_generate_passes_regional_flag_and_records_it_without_lean(tmp_path, monkeypatch):
    row, config = _task(tmp_path)
    source = lean_source.render_candidate_scaffold(row).replace("skip", "have unused := h")
    monkeypatch.setattr(native, "configure_native_environment", lambda **_: {})
    monkeypatch.setattr(native, "_inventory", lambda *args: (
        _scan(source, ["have unused := h", "exact h"]) | {
            "declaration_end_byte": len(source[:source.index(lean_source.TARGET_END)].rstrip().encode())}, {}))
    candidates = native.generate(config, source, tmp_path / "boundary", regional=True)
    assert any(item["family"] == "native-regional-unused-local" for item in candidates)
    assert json.loads((tmp_path / "boundary/native-proposals.json").read_text())["regional"] is True


def test_regional_is_bounded_deterministic_and_never_claims_validation():
    source = "theorem target (p : Prop) (h : p) : p := by\n  have x := h\n  have y := x\n  clear y\n  exact h"
    scan = _scan(source, ["have x := h", "have y := x", "clear y", "exact h"])
    first = native.proposals_from_inventory(source, scan, regional=True, max_candidates=3)
    assert first == native.proposals_from_inventory(source, scan, regional=True, max_candidates=3)
    assert len(first) == len({item["source_sha256"] for item in first}) == 3
    assert all(item["validation_required"] == "complete_source_exact_axioms_and_compatibility" for item in first)
    assert native.proposals_from_inventory(source, scan, regional=True, max_candidates=0) == []


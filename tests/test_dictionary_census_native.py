"""Opt-in synthetic Lean checks; use an existing toolchain, never build packages."""
import json
import os
from pathlib import Path
import subprocess

import pytest

from e6.deterministic_support import dictionary_cache as g


FIXTURE = r"""
open Lean Elab Command Meta PrettyPrinter.Delaborator SubExpr

class HeartbeatDictionary where
  value : Nat
def slowDictionary (xs : List Nat) : HeartbeatDictionary := ⟨xs.length⟩
def fastDictionary (xs : List Nat) : HeartbeatDictionary := ⟨xs.length⟩
def useDictionary (_ : HeartbeatDictionary) : True := True.intro
def keepProofs (_ _ _ _ : True) : True := True.intro

syntax "dictionary_timeout%" term : term
elab_rules : term
  | `(dictionary_timeout% $arg) => do
    let _ ← mkFreshExprMVar (mkConst ``True)
    IO.addHeartbeats 1000001
    Core.checkSystem "dictionary-timeout-fixture"
    Term.elabTerm (← `(slowDictionary $arg)) none

@[delab app.slowDictionary] meta def delabSlowDictionary : Delab := do
  let arg ← withNaryArg 0 delab
  `(dictionary_timeout% $arg)

meta def runIsolated (action : MetaM Json) (outerLimit := 20000000) (beforeEntry := 0) : MetaM (Except Exception Json) := do
  let ctx ← readThe Core.Context
  let state ← getThe Core.State
  let started ← IO.getNumHeartbeats
  let test : MetaM Json := do
    IO.addHeartbeats beforeEntry
    E6GenericDictionaryCensus.withRoundTripHeartbeats action
  return ← (test.run'.run'
    {ctx with initHeartbeats := started, maxHeartbeats := outerLimit} state).toIO'

meta def isHeartbeatError (result : Except Exception Json) : Bool :=
  match result with | .error e => e.isMaxHeartbeat | _ => false

run_cmd liftTermElabM do
  -- A real nested smaller budget is not the entry's owned limit.
  let nested ← runIsolated <| Core.withCurrHeartbeats <|
    withTheReader Core.Context (fun c => {c with maxHeartbeats := 10}) do
      IO.addHeartbeats 11
      Core.checkSystem "nested-budget-fixture"
      pure Json.null
  unless isHeartbeatError nested do
    throwError "nested heartbeat was swallowed"
  -- A tagged heartbeat without consuming the owned allowance also propagates.
  let foreign ← runIsolated do
    Core.throwMaxHeartbeat `foreign `maxHeartbeats 1
    pure Json.null
  unless isHeartbeatError foreign do
    throwError "unowned heartbeat was swallowed"
  for tag in [`runtime.maxRecDepth, `runtime.outOfMemory] do
    let result ← runIsolated do
      IO.addHeartbeats 1000001
      throw <| Exception.error Syntax.missing (.tagged tag m!"synthetic resource failure")
    unless result matches .error _ do throwError "non-heartbeat resource was swallowed"
  let interrupt ← runIsolated throwInterruptException
  unless (match interrupt with | .error e => e.isInterrupt | _ => false) do
    throwError "interrupt was swallowed"
  -- Even a local timeout must not hide the enclosing census budget.
  let outer ← runIsolated (outerLimit := 500000) do
    IO.addHeartbeats 1000001
    Core.checkSystem "local-budget-fixture"
    pure Json.null
  unless isHeartbeatError outer do throwError "outer budget was swallowed"
  let late ← runIsolated (outerLimit := 500000) do
    IO.addHeartbeats 500001
    pure Json.null
  unless isHeartbeatError late do throwError "successful action hid outer budget"
  let expired ← runIsolated (outerLimit := 1) (beforeEntry := 2) (pure Json.null)
  unless isHeartbeatError expired do throwError "expired outer budget was ignored"
  -- roundTrip's existing finally must restore metavariables created by a timeout.
  let env ← getEnv
  let value ← Term.elabTerm (← `(slowDictionary [1, 2, 3, 4])) none
  let type ← inferType value
  let before := (← getMCtx).decls.toList.length
  let result ← E6GenericDictionaryCensus.withRoundTripHeartbeats <|
    E6GenericDictionaryCensus.roundTrip ⟨value, type, 4, 20, "compound", true⟩ env
  unless (result.getObjValAs? String "status").toOption == some "failed" do
    throwError "local roundtrip timeout was not skipped"
  unless (← getMCtx).decls.toList.length == before do throwError "roundtrip leaked metavariables"
"""


@pytest.mark.skipif(not os.environ.get("HARNESS_DICTIONARY_LEAN"),
    reason="set HARNESS_DICTIONARY_LEAN to an existing cached Lean executable")
def test_owned_roundtrip_timeout_continues_bounded_census_with_context_guards(tmp_path):
    lean = Path(os.environ["HARNESS_DICTIONARY_LEAN"]).resolve()
    assert lean.is_file()
    helper = (g.SUPPORT / "DictionaryCensus.lean.inc").read_text(encoding="utf-8")
    # The longest first entry times out; five later distinct dictionaries remain.
    groups = []
    for index, length in enumerate(range(12, 6, -1)):
        term = ("slowDictionary" if index == 0 else "fastDictionary") + " [" + ", ".join(
            str(number) for number in range(length)) + "]"
        groups.append("keepProofs " + " ".join(f"(useDictionary ({term}))" for _ in range(4)))
    body = "keepProofs " + " ".join(f"({group})" for group in groups[:3]) + " (keepProofs " + " ".join(
        f"({group})" for group in groups[3:]) + " True.intro)"
    declaration = "theorem dictionaryHeartbeatTarget : True := by\n  exact " + body + "\n"
    row = {"name": "dictionaryHeartbeatTarget", "signature": "theorem dictionaryHeartbeatTarget : True"}
    site = g.target_site(row, declaration)
    output = tmp_path / "dictionary-census.json"
    command = f"#e6_generic_dictionary_census {json.dumps(str(output))} after {site['proof_offset_bytes']} in\n"
    lead = "import Lean\nmeta section\n" + helper + "\nend\n" + FIXTURE + "\n"
    source = lead + command + declaration
    path = tmp_path / "DictionaryHeartbeat.lean"
    path.write_text(source, encoding="utf-8")
    # The executable resolves its installed Lean library; no lake/config build.
    environment = {key: value for key, value in os.environ.items() if key in {"PATH", "HOME", "LANG", "LC_ALL"}}
    environment.update(LEAN_NUM_THREADS="1", OMP_NUM_THREADS="1")
    run = subprocess.run([str(lean), str(path)], env=environment, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    (tmp_path / "compile.log").write_text(run.stdout, encoding="utf-8")
    assert run.returncode == 0, run.stdout
    scan = json.loads(output.read_text(encoding="utf-8"))
    assert scan["status"] == scan["analysis"]["status"] == "completed"
    assert scan["target_absent_from_analysis_env"] is True
    assert scan["root_context_kind"] == "original_by_tactic_info"
    assert scan["local_instance_context"] == "captured_original_root_goal"
    assert scan["opened_proof_lambdas"] is False
    analysis = scan["analysis"]
    assert analysis["roundtrip_attempt_count"] == 4
    assert analysis["proving_calls"] == 0
    trips = [record["roundtrip"] for record in analysis["records"] if record["candidate_heuristic"]]
    assert [trip["status"] for trip in trips] == ["failed", "passed", "passed", "passed", "not_attempted", "not_attempted"]
    assert trips[0]["max_heartbeat"] is True
    assert trips[0]["heartbeat_limit_scope"] == "dictionary_roundtrip"
    binding = {"harness_root_start_byte": len((lead + command).encode()) + site["proof_offset_bytes"],
        "harness_declaration_end_byte": len(source.rstrip("\n").encode())}
    proposals = g.proposals(declaration, row, site, scan, binding, 4)
    assert len(proposals) == 3
    assert all(proposal["census_record_index"] != 0 and proposal["parent_sha256"] == g.digest(declaration)
        for proposal in proposals)


@pytest.mark.skipif(not os.environ.get("HARNESS_DICTIONARY_LEAN"),
    reason="set HARNESS_DICTIONARY_LEAN to an existing cached Lean executable")
@pytest.mark.parametrize("module", [False, True])
def test_capture_keeps_scoped_names_instances_and_original_root(tmp_path, monkeypatch, module):
    from types import SimpleNamespace
    lean = Path(os.environ["HARNESS_DICTIONARY_LEAN"]).resolve()
    assert lean.is_file()
    header = "module\n\npublic import Lean\n" if module else "import Lean\n"
    prefix = header + """
namespace DictionaryScopeFixture
class HasWitness (α : Type) where
  value : Nat
scoped instance (α : Type) : HasWitness α := ⟨17⟩
def marker : Nat := 17
end DictionaryScopeFixture
variable (unused : Nat)
-- α: command-scoped imports and instances must reach the original theorem.
set_option maxHeartbeats 2000000 in
omit unused in
open scoped DictionaryScopeFixture in
open DictionaryScopeFixture in
"""
    declaration = "theorem dictionaryScopeTarget (α : Type) : marker = (inferInstance : HasWitness α).value := by\n  rfl\n"
    row = {"name": "dictionaryScopeTarget", "signature": declaration.split(" :=")[0]}
    site = g.target_site(row, declaration)
    config = {"primary": str(tmp_path), "root": str(tmp_path), "task_sha256": "a" * 64}
    monkeypatch.setattr(g.lean_source, "exact_source_prefix", lambda *_: SimpleNamespace(text=prefix, sha256=g.digest(prefix)))
    monkeypatch.setattr(g.RuntimeContext, "resolve", lambda *_: SimpleNamespace(environment=lambda _: {}))
    monkeypatch.setattr(g, "configure_native_environment", lambda **_: {})
    monkeypatch.setattr(g.lean_launch, "workspace_guard", lambda *_: {"synthetic_stdlib_fixture": True})
    def run(path, _project, _deadline, log):
        environment = {key: value for key, value in os.environ.items() if key in {"PATH", "HOME", "LANG", "LC_ALL"}}
        environment.update(LEAN_NUM_THREADS="1", OMP_NUM_THREADS="1")
        completed = subprocess.run([str(lean), "-D", "experimental.module=true", str(path)],
            env=environment, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
        log.write_text(completed.stdout, encoding="utf-8")
        return {"returncode": completed.returncode, "timed_out": False, "seconds": 0}
    monkeypatch.setattr(g.native, "_run", run)
    scan, binding = g.capture(config, declaration, row, site, tmp_path, 30)
    assert scan["status"] == scan["analysis"]["status"] == "completed"
    assert scan["target_absent_from_analysis_env"] is True
    assert scan["root_context_kind"] == "original_by_tactic_info"
    assert scan["local_instance_context"] == "captured_original_root_goal"
    assert scan["opened_proof_lambdas"] is False
    assert scan["root_start_byte"] == binding["harness_root_start_byte"]
    assert scan["analysis"]["proving_calls"] == 0

"""Bounded, source-bound residual goals from Lean's structured unsolved-goal log.

An ``ofGoal`` carries a metavariable and a frozen context from the instant Lean
reported the open case. Text diagnostics and historical tactic entry states are
never treated as residual state. The captured context also serves retrieval, so
inspecting or searching a case requires no further elaboration.
"""
from __future__ import annotations

import hashlib
import json
import re
import time
from pathlib import Path
from typing import Any

from lean_tools.feedback_workflow import bind_feedback_scoring_policy
from lean_tools import arena_workflow as arena, lean_goal_state, lean_source

MARKER = "__LRH_UNFINISHED_CASES_V1__"
DEFAULT_LIMIT = 6
MAX_LIMIT = 12
MAX_CASES = 128
EXTRACTION_SECONDS = 15
DEFAULT_REQUEST_SECONDS = 60
MAX_REQUEST_SECONDS = 60
MAX_CONTEXT_CHARS = 64000
TOOL = {
    "name": "unfinished_cases",
    "description": "List bounded actual open cases for the current candidate SHA256; optional goal_id inspects one full context. Uses structured residual Lean goals, never historical entry goals; unavailable means no reliable residual state. Read-only; no checkpoint or search. Default 6 cases, maximum 12. Explicit extraction timeout_seconds defaults to 60, maximum 60; automatic failed-edit extraction remains capped at 15 seconds.",
    "inputSchema": {
        "type": "object", "properties": {
            "candidate": {"type": "string"},
            "expected_sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
            "goal_id": {"type": "string", "pattern": "^goal-[0-9a-f]{64}$"},
            "limit": {"type": "integer", "minimum": 1, "maximum": MAX_LIMIT},
            "timeout_seconds": {"type": "number", "exclusiveMinimum": 0, "maximum": MAX_REQUEST_SECONDS, "default": DEFAULT_REQUEST_SECONDS},
        }, "required": ["expected_sha256"], "additionalProperties": False,
    },
}

# No new import: define the helper after existing imports and replay the exact
# original prefix before the unchanged target, including scoped `... in` forms.
# Escaped local names resist prefix-installed keywords;
# explicit pattern binders resist constructors from opened namespaces. Root API
# names resist namespace capture. Positions are deterministic for the snapshot.
_WRAPPER = r'''
elab "__COMMAND__ " «lrhResidual_cmd»:command : command => do
  let «lrhResidual_declarationStart» ← match «lrhResidual_cmd».raw.getPos? with
    | _root_.Option.some «lrhResidual_position»@_ => _root_.Pure.pure «lrhResidual_position».byteIdx
    | _root_.Option.none => throwError "target command has no source start"
  let «lrhResidual_declarationEnd» ← match «lrhResidual_cmd».raw.getTailPos? with
    | _root_.Option.some «lrhResidual_position»@_ => _root_.Pure.pure «lrhResidual_position».byteIdx
    | _root_.Option.none => throwError "target command has no source end"
  let «lrhResidual_previousMessages» := ((← _root_.MonadStateOf.get) : _root_.Lean.Elab.Command.State).messages.toList.length
  _root_.Lean.logInfo (_root_.Lean.ToMessageData.toMessageData ("__MARKER__" ++ "{\"stage\":\"target_started\"}"))
  _root_.Lean.Elab.Command.elabCommand «lrhResidual_cmd»
  _root_.Lean.logInfo (_root_.Lean.ToMessageData.toMessageData ("__MARKER__" ++ "{\"stage\":\"target_finished\"}"))
  let rec «lrhResidual_collect» («lrhResidual_fuel» : _root_.Nat) («lrhResidual_ctx» : _root_.Option _root_.Lean.MessageDataContext)
      («lrhResidual_active» : _root_.Bool) («lrhResidual_data» : _root_.Lean.MessageData) : _root_.IO (_root_.Array (_root_.Lean.MessageDataContext × _root_.Lean.MVarId)) := do
    match «lrhResidual_fuel» with
    | 0 => throw (_root_.IO.userError "structured residual message traversal limit")
    | _root_.Nat.succ «lrhResidual_fuel»@_ =>
      match «lrhResidual_data» with
      | .withContext «lrhResidual_c»@_ «lrhResidual_child»@_ => «lrhResidual_collect» «lrhResidual_fuel» (_root_.Option.some «lrhResidual_c») «lrhResidual_active» «lrhResidual_child»
      | .withNamingContext _ «lrhResidual_child»@_ => «lrhResidual_collect» «lrhResidual_fuel» «lrhResidual_ctx» «lrhResidual_active» «lrhResidual_child»
      | .tagged «lrhResidual_tag»@_ «lrhResidual_child»@_ => «lrhResidual_collect» «lrhResidual_fuel» «lrhResidual_ctx» («lrhResidual_active» || «lrhResidual_tag» == `Tactic.unsolvedGoals) «lrhResidual_child»
      | .compose «lrhResidual_left»@_ «lrhResidual_right»@_ => return (← «lrhResidual_collect» «lrhResidual_fuel» «lrhResidual_ctx» «lrhResidual_active» «lrhResidual_left») ++ (← «lrhResidual_collect» «lrhResidual_fuel» «lrhResidual_ctx» «lrhResidual_active» «lrhResidual_right»)
      | .nest _ «lrhResidual_child»@_ | .group «lrhResidual_child»@_ | .ofWidget _ «lrhResidual_child»@_ => «lrhResidual_collect» «lrhResidual_fuel» «lrhResidual_ctx» «lrhResidual_active» «lrhResidual_child»
      | .ofGoal «lrhResidual_goal»@_ =>
        if «lrhResidual_active» then
          if let _root_.Option.some «lrhResidual_ctx»@_ := «lrhResidual_ctx» then return #[(«lrhResidual_ctx», «lrhResidual_goal»)]
          else throw (_root_.IO.userError "residual goal without a frozen context")
        else return #[]
      | .ofLazy «lrhResidual_f»@_ _ =>
        let «lrhResidual_value» ← «lrhResidual_f» _root_.Option.none
        if let _root_.Option.some «lrhResidual_child»@_ := «lrhResidual_value».get? _root_.Lean.MessageData then «lrhResidual_collect» «lrhResidual_fuel» «lrhResidual_ctx» «lrhResidual_active» «lrhResidual_child»
        else throw (_root_.IO.userError "unrecognized structured residual lazy message")
      | _ => return #[]
  let mut «lrhResidual_cases» : _root_.Array _root_.Lean.Json := #[]
  let mut «lrhResidual_total» := 0
  let mut «lrhResidual_occurrence» := 0
  let «lrhResidual_fileMap» ← _root_.Lean.MonadFileMap.getFileMap
  let «lrhResidual_currNamespace» ← _root_.Lean.MonadResolveName.getCurrNamespace
  let «lrhResidual_openDecls» ← _root_.Lean.MonadResolveName.getOpenDecls
  let «lrhResidual_ngen» := ((← _root_.MonadStateOf.get) : _root_.Lean.Elab.Command.State).ngen
  for «lrhResidual_message»@_ in (((← _root_.MonadStateOf.get) : _root_.Lean.Elab.Command.State).messages.toList.drop «lrhResidual_previousMessages») do
    let «lrhResidual_location» := «lrhResidual_fileMap».ofPosition «lrhResidual_message».pos
    if «lrhResidual_declarationStart» <= «lrhResidual_location».byteIdx && «lrhResidual_location».byteIdx <= «lrhResidual_declarationEnd» && «lrhResidual_message».data.kind == `Tactic.unsolvedGoals then
      let «lrhResidual_goals» ← «lrhResidual_collect» 10000 _root_.Option.none false «lrhResidual_message».data
      if !«lrhResidual_goals».isEmpty then
        let mut «lrhResidual_index» := 0
        for («lrhResidual_context»@_, «lrhResidual_goal»@_) in «lrhResidual_goals» do
          «lrhResidual_total» := «lrhResidual_total» + 1
          if «lrhResidual_cases».size < __MAX_CASES__ then
            let «lrhResidual_info» : _root_.Lean.Elab.ContextInfo := {
              env := «lrhResidual_context».env
              mctx := «lrhResidual_context».mctx
              options := «lrhResidual_context».opts
              fileMap := «lrhResidual_fileMap», currNamespace := «lrhResidual_currNamespace», openDecls := «lrhResidual_openDecls», ngen := «lrhResidual_ngen» }
            let «lrhResidual_value» ← «lrhResidual_info».runMetaM «lrhResidual_context».lctx do
              «lrhResidual_goal».withContext do
                if ← «lrhResidual_goal».isAssigned then throwError "reported residual goal was already assigned"
                let «lrhResidual_render» («lrhResidual_expr» : _root_.Lean.Expr) : _root_.Lean.Meta.MetaM _root_.String := do
                  _root_.Lean.MonadWithOptions.withOptions (fun «lrhResidual_opts»@_ => _root_.Lean.Option.set ((«lrhResidual_opts».setBool `pp.deepTerms true).setBool `pp.proofs true) _root_.Lean.pp.maxSteps 1000000000) do
                    _root_.Pure.pure (_root_.ToString.toString (← _root_.Lean.Meta.ppExpr (← _root_.Lean.instantiateMVars «lrhResidual_expr»)))
                let «lrhResidual_targetExpr» ← _root_.Lean.instantiateMVars (← «lrhResidual_goal».getType)
                let «lrhResidual_target» ← «lrhResidual_render» «lrhResidual_targetExpr»
                let mut «lrhResidual_hypotheses» : _root_.Array _root_.String := #[]
                let «lrhResidual_conclusions» := «lrhResidual_targetExpr».getUsedConstants
                let mut «lrhResidual_hypConstants» : _root_.Array _root_.Lean.Name := #[]
                for «lrhResidual_decl»@_ in (← _root_.Lean.MonadLCtx.getLCtx) do
                  if !«lrhResidual_decl».isImplementationDetail then
                    let «lrhResidual_hypType» ← «lrhResidual_render» «lrhResidual_decl».type
                    let «lrhResidual_valueText» ← match «lrhResidual_decl».value? (allowNondep := true) with
                      | _root_.Option.none => _root_.Pure.pure ""
                      | _root_.Option.some «lrhResidual_value»@_ => do _root_.Pure.pure (" := " ++ (← «lrhResidual_render» «lrhResidual_value»))
                    «lrhResidual_hypotheses» := «lrhResidual_hypotheses».push s!"{«lrhResidual_decl».userName} : {«lrhResidual_hypType»}{«lrhResidual_valueText»}"
                    for «lrhResidual_name»@_ in (← _root_.Lean.instantiateMVars «lrhResidual_decl».type).getUsedConstants do
                      if !«lrhResidual_hypConstants».contains «lrhResidual_name» then «lrhResidual_hypConstants» := «lrhResidual_hypConstants».push «lrhResidual_name»
                if «lrhResidual_target».length + («lrhResidual_hypotheses».foldl (fun «lrhResidual_n»@_ «lrhResidual_text»@_ => «lrhResidual_n» + «lrhResidual_text».length) 0) > __MAX_CONTEXT__ then
                  throwError "residual case context exceeds the bounded extraction limit"
                let «lrhResidual_generic» : _root_.Array _root_.String := #["Eq", "HEq", "Iff", "And", "Or", "Not", "Exists", "True", "False", "Nat", "Int", "Bool", "OfNat.ofNat", "OfNat", "LT.lt", "LE.le", "HAdd.hAdd", "HMul.hMul", "HSub.hSub", "HDiv.hDiv", "Neg.neg", "Membership.mem", "Decidable", "DecidableEq", "instDecidableEqNat"]
                let mut «lrhResidual_symbols» : _root_.Array _root_.Lean.Json := #[]
                let mut «lrhResidual_names» := «lrhResidual_conclusions»
                for «lrhResidual_name»@_ in «lrhResidual_hypConstants» do
                  if !«lrhResidual_names».contains «lrhResidual_name» then «lrhResidual_names» := «lrhResidual_names».push «lrhResidual_name»
                «lrhResidual_names» := «lrhResidual_names».qsort (fun «lrhResidual_a»@_ «lrhResidual_b»@_ => «lrhResidual_a».toString < «lrhResidual_b».toString)
                for «lrhResidual_name»@_ in «lrhResidual_names».take 128 do
                  let «lrhResidual_c» := «lrhResidual_conclusions».contains «lrhResidual_name»
                  let «lrhResidual_h» := «lrhResidual_hypConstants».contains «lrhResidual_name»
                  let «lrhResidual_g» := «lrhResidual_generic».contains «lrhResidual_name».toString
                  let «lrhResidual_weight» := (if «lrhResidual_c» then (if «lrhResidual_g» then 2 else 12) else 0) + (if «lrhResidual_h» then (if «lrhResidual_g» then 1 else 3) else 0)
                  «lrhResidual_symbols» := «lrhResidual_symbols».push (_root_.Lean.Json.mkObj [("name", _root_.Lean.ToJson.toJson «lrhResidual_name».toString), ("weight", _root_.Lean.ToJson.toJson «lrhResidual_weight»), ("conclusion", _root_.Lean.ToJson.toJson «lrhResidual_c»), ("hypothesis", _root_.Lean.ToJson.toJson «lrhResidual_h»), ("generic", _root_.Lean.ToJson.toJson «lrhResidual_g»)])
                return _root_.Lean.Json.mkObj [("target", _root_.Lean.ToJson.toJson «lrhResidual_target»), ("hypotheses", _root_.Lean.ToJson.toJson «lrhResidual_hypotheses»), ("case_name", _root_.Lean.ToJson.toJson (← «lrhResidual_goal».getDecl).userName.toString), ("context_symbols", _root_.Lean.ToJson.toJson «lrhResidual_symbols»), ("context_symbols_total", _root_.Lean.ToJson.toJson «lrhResidual_names».size), ("context_symbols_truncated", _root_.Lean.ToJson.toJson (decide («lrhResidual_names».size > 128))), ("occurrence", _root_.Lean.ToJson.toJson «lrhResidual_occurrence»), ("index", _root_.Lean.ToJson.toJson «lrhResidual_index»), ("position_byte", _root_.Lean.ToJson.toJson «lrhResidual_location».byteIdx)]
            «lrhResidual_cases» := «lrhResidual_cases».push «lrhResidual_value»
          «lrhResidual_index» := «lrhResidual_index» + 1
        «lrhResidual_occurrence» := «lrhResidual_occurrence» + 1
  _root_.Lean.logInfo (_root_.Lean.ToMessageData.toMessageData ("__MARKER__" ++ (_root_.Lean.Json.mkObj [("status", _root_.Lean.ToJson.toJson (if «lrhResidual_total» == 0 then "none" else "ok")), ("cases", _root_.Lean.ToJson.toJson «lrhResidual_cases»), ("total_cases", _root_.Lean.ToJson.toJson «lrhResidual_total»)]).compress))
'''

_HELPER_END = "\n-- LRH residual helper end\n"


def _sha(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def build_harness(prefix: str, declaration: str) -> tuple[str, int]:
    # Stable helper bytes preserve resident snapshots for the expensive original
    # prefix across candidate edits. Runtime syntax supplies the unchanged target
    # span; Python separately validates every reported byte against this snapshot.
    command = "lrhUnfinished" + _sha(prefix.encode())[:16]
    helper = _WRAPPER.replace("__COMMAND__", command).replace("__MARKER__", MARKER).replace("__MAX_CASES__", str(MAX_CASES)).replace("__MAX_CONTEXT__", str(MAX_CONTEXT_CHARS)) + _HELPER_END
    header_end, _module = lean_source.import_header_end(prefix)
    header, body_prefix = prefix[:header_end], prefix[header_end:]
    suffix = "\nset_option Elab.async false in\n" + command + " "
    start = len((header + helper + body_prefix + suffix).encode())
    end = start + len(declaration.encode())
    if end >= 10 ** 12:
        raise ValueError("generated source is too large")
    return header + helper + body_prefix + suffix + declaration + "\n", start


def _validate(request: Any) -> int:
    if not isinstance(request, dict) or set(request) - set(TOOL["inputSchema"]["properties"]):
        raise ValueError("request contains an unsupported unfinished_cases field")
    if not isinstance(request.get("expected_sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", request["expected_sha256"]):
        raise ValueError("expected_sha256 must be the current candidate's lowercase SHA256")
    if "goal_id" in request and (not isinstance(request["goal_id"], str) or not re.fullmatch(r"goal-[0-9a-f]{64}", request["goal_id"])):
        raise ValueError("goal_id must be a source-bound handle returned by unfinished_cases")
    limit = request.get("limit", DEFAULT_LIMIT)
    if type(limit) is not int or not 1 <= limit <= MAX_LIMIT:
        raise ValueError(f"limit must be an integer in 1..{MAX_LIMIT}")
    timeout = request.get("timeout_seconds", DEFAULT_REQUEST_SECONDS)
    if type(timeout) not in {int, float} or not 0 < timeout <= MAX_REQUEST_SECONDS:
        raise ValueError(f"timeout_seconds must be positive and at most {MAX_REQUEST_SECONDS}")
    return limit


def _binding(feedback: Any, digest: str, prefix: lean_source.SourcePrefix) -> dict[str, Any]:
    registry = feedback.settings.get("fingerprint_registry")
    fingerprint = arena.measurement_environment_fingerprint(
        feedback.row, feedback.project, registry_path=Path(registry) if registry else None)
    return {"source_sha256": digest, "prefix_sha256": prefix.sha256,
            "environment_fingerprint": fingerprint,
            "project_root": str(Path(feedback.project).resolve()),
            "task": feedback.row["name"], "task_signature": feedback.row["signature"],
            "extractor_sha256": _sha(_WRAPPER.encode())}


def _validate_record(record: Any, declaration: str, declaration_byte: int) -> dict[str, Any]:
    if (not isinstance(record, dict) or record.get("status") not in {"ok", "none"}
            or not isinstance(record.get("cases"), list)
            or len(record["cases"]) > MAX_CASES
            or type(record.get("total_cases")) is not int
            or record["total_cases"] < len(record["cases"])
            or len(record["cases"]) != min(MAX_CASES, record["total_cases"])):
        raise ValueError("Lean did not return a bounded structured residual-case record")
    if (record["status"] == "none") != (record["total_cases"] == 0):
        raise ValueError("Lean returned inconsistent residual case counts")
    seen = set()
    for case in record["cases"]:
        if (not isinstance(case, dict) or not isinstance(case.get("target"), str)
                or not isinstance(case.get("case_name"), str)
                or not isinstance(case.get("hypotheses"), list)
                or any(not isinstance(item, str) for item in case["hypotheses"])
                or type(case.get("position_byte")) is not int
                or type(case.get("occurrence")) is not int or case["occurrence"] < 0
                or type(case.get("index")) is not int or case["index"] < 0):
            raise ValueError("Lean returned malformed residual goal context")
        context_text = case["target"] + "".join(case["hypotheses"])
        if len(context_text) > MAX_CONTEXT_CHARS or "⋯" in context_text:
            raise ValueError("Lean returned incomplete or over-limit residual goal context")
        local_byte = case["position_byte"] - declaration_byte
        if not 0 <= local_byte <= len(declaration.encode()):
            raise ValueError("residual goal observation is outside the target declaration")
        declaration.encode()[:local_byte].decode("utf-8")  # reject split code points
        identity = (case["occurrence"], case["index"])
        if identity in seen:
            raise ValueError("Lean returned duplicate residual goal identities")
        seen.add(identity)
        symbols = case.get("context_symbols")
        if (not isinstance(symbols, list) or len(symbols) > 128
                or any(not isinstance(symbol, dict) or not isinstance(symbol.get("name"), str)
                       or type(symbol.get("weight")) is not int or symbol["weight"] < 1
                       or type(symbol.get("conclusion")) is not bool
                       or type(symbol.get("hypothesis")) is not bool for symbol in symbols)
                or len({symbol["name"] for symbol in symbols}) != len(symbols)):
            raise ValueError("Lean returned malformed residual context constants")
    return record


def _record_for_retrieval(case: dict[str, Any], count: int) -> dict[str, Any]:
    return {"status": "ok", "goal_count": count, "selected_goal_index": case["index"],
            "rendered_goals": [case["target"]], "rendered_hypotheses": case["hypotheses"],
            "rendered_hypotheses_by_goal": [case["hypotheses"]],
            **{key: case[key] for key in ("context_symbols", "context_symbols_total", "context_symbols_truncated")}}


def _diagnostic_region(item: dict[str, Any], source: str, helper_span: tuple[int, int, int],
                       declaration_byte: int) -> str | None:
    """Locate a raw Lean diagnostic without treating diagnostic text as a goal."""
    pos = item.get("pos")
    lsp = not isinstance(pos, dict)
    if lsp:
        raw_line, column = item.get("line"), item.get("character")
        line = raw_line + 1 if type(raw_line) is int else None
    else:
        line, column = pos.get("line"), pos.get("column")
    lines = source.splitlines(keepends=True)
    if (type(line) is not int or type(column) is not int or column < 0
            or not 1 <= line <= len(lines)):
        return None
    # --json columns are zero based. Only the target's first line shares a
    # wrapper invocation; its generated command token contains ASCII only.
    if lsp:
        try:
            line_prefix = lines[line - 1].encode("utf-16-le")[:column * 2].decode("utf-16-le")
        except UnicodeDecodeError:
            return None
    else:
        line_prefix = lines[line - 1][:column]
    offset = len("".join(lines[:line - 1]).encode()) + len(line_prefix.encode())
    helper_start, helper_end, wrapper_start = helper_span
    if helper_start <= offset < helper_end or wrapper_start <= offset < declaration_byte:
        return "helper"
    return "prefix" if offset < declaration_byte else "candidate"


def _failure_kind(observed: dict[str, Any], source: str, helper_span: tuple[int, int, int],
                  declaration_byte: int, stages: list[str]) -> str:
    if observed.get("timed_out") or any(item.get("code") == "discovery_timeout"
                                        for item in observed.get("diagnostics", []) if isinstance(item, dict)):
        return "extraction_timeout"
    if observed.get("backend_error"):
        return "backend_error"
    regions = {_diagnostic_region(item, source, helper_span, declaration_byte)
               for item in observed.get("diagnostics", []) if isinstance(item, dict)
               and item.get("severity") not in {"warning", 2}}
    if "prefix" in regions:
        return "prefix_error"
    if "target_started" not in stages and "helper" in regions:
        return "helper_error"
    if "target_finished" in stages:
        # A finished helper with a valid `none` record is handled separately;
        # no record after this stage means extraction itself failed.
        return "helper_error"
    if "candidate" in regions or "target_started" in stages:
        return "candidate_error"
    return "no_structured_state"


def _diagnostic_preview(item: dict[str, Any]) -> dict[str, Any]:
    # run_harness preserves raw `data` for durable evidence. Never duplicate its
    # potentially large contents into the bounded inline residual response.
    result = {key: item[key] for key in ("pos", "endPos", "line", "character") if key in item}
    result.update({key: str(item[key])[:160] for key in ("code", "severity", "kind") if key in item})
    result["message"] = str(item.get("message", ""))[:400]
    return result


def _observe(feedback: Any, candidate: Path, raw: bytes, snapshot_path: Path,
             limit: int, *, timeout_seconds: float = EXTRACTION_SECONDS,
             request_mode: str = "automatic_failed_edit") -> dict[str, Any]:
    from lean_tools import goal_retrieval
    digest = _sha(raw)
    text = lean_source.candidate_text_from_bytes(raw)
    snapshot = lean_source.snapshot_candidate(feedback.row, text, candidate)
    revision = lean_goal_state.source_revision(candidate)
    prefix = lean_source.exact_source_prefix(feedback.row, feedback.project)
    binding = _binding(feedback, digest, prefix)
    cache_key = _sha(json.dumps(binding, sort_keys=True).encode())
    root = Path(getattr(feedback, "root", candidate.parent))
    path = root / ".feedback" / "unfinished-cases" / f"{cache_key}.json"
    source, declaration_byte = build_harness(prefix.text, snapshot.declaration)
    header_end, _module = lean_source.import_header_end(prefix.text)
    helper_start = len(prefix.text[:header_end].encode())
    generated = source.encode()
    helper_span = (helper_start, generated.index(_HELPER_END.encode(), helper_start) + len(_HELPER_END.encode()),
                   generated.rindex(b"\nset_option Elab.async false in\n", 0, declaration_byte))
    extraction_timeout = min(feedback.timeout, timeout_seconds)
    cache_hit = False
    try:
        saved = json.loads(path.read_text(encoding="utf-8"))
        if saved["binding"] != binding or saved["generated_source_sha256"] != _sha(source.encode()):
            raise ValueError("residual cache identity mismatch")
        if isinstance(saved.get("unavailable"), dict):
            failure = saved["unavailable"]
            if (failure.get("failure_kind") == "extraction_timeout"
                    and extraction_timeout > failure.get("extraction_timeout_seconds", 0)):
                raise ValueError("retrying a bounded extraction timeout with a larger requested budget")
            return {**saved["unavailable"], "cache_hit": True, "details_path": str(path),
                    "requested_extraction_timeout_seconds": extraction_timeout, "request_mode": request_mode}
        record = _validate_record(saved["record"], snapshot.declaration, declaration_byte)
        cache_hit = True
    except (OSError, ValueError, KeyError, TypeError):
        from lean_tools.feedback_workflow import atomic_text
        try:
            observed = goal_retrieval.run_harness(source, feedback.project, extraction_timeout, marker=MARKER)
        except goal_retrieval.persistent.PersistentQuickError as error:
            detail = getattr(error, "result", None)
            detail = detail if isinstance(detail, dict) else {}
            timed_out = bool(detail.get("timed_out")) or bool(re.search(r"timeout|timed out|deadline|expired", str(error), re.I))
            observed = {"records": [], "diagnostics": [{"code": "discovery_timeout" if timed_out else "residual_backend_error",
                                                         "message": str(error)}],
                        "backend": "resident", "backend_error": True, "timed_out": timed_out,
                        "failure_phase": detail.get("failure_phase"), "backend_failure": detail,
                        "seconds": detail.get("wall_seconds", detail.get("lsp_seconds")),
                        "queue_wait_seconds": detail.get("queue_wait_seconds")}
        stages = [item["stage"] for item in observed.get("records", [])
                  if isinstance(item, dict) and item.get("stage") in {"target_started", "target_finished"}]
        records = [item for item in observed.get("records", [])
                   if not isinstance(item, dict) or "stage" not in item]
        failure_kind = _failure_kind(observed, source, helper_span, declaration_byte, stages)
        try:
            error_regions = {_diagnostic_region(item, source, helper_span, declaration_byte)
                             for item in observed.get("diagnostics", []) if isinstance(item, dict)
                             and item.get("severity") not in {"warning", 2}}
            if "prefix" in error_regions or "helper" in error_regions:
                failure_kind = "prefix_error" if "prefix" in error_regions else "helper_error"
                raise ValueError("Lean reported an error in the residual inspection infrastructure")
            if len(records) != 1:
                raise ValueError("Lean did not expose reliable structured residual goals")
            record = _validate_record(records[0], snapshot.declaration, declaration_byte)
            if record["status"] == "none" and any(item.get("severity") not in {"warning", 2}
                                                  for item in observed.get("diagnostics", []) if isinstance(item, dict)):
                failure_kind = "candidate_error"
                raise ValueError("Lean reported no structured residual state while elaboration diagnostics remain")
        except (ValueError, KeyError, TypeError) as error:
            reasons = {
                "helper_error": "generated residual helper failed to parse, elaborate, or extract a structured record",
                "prefix_error": "the exact legal prefix reported an error before residual inspection",
                "candidate_error": "candidate elaboration failed without usable structured residual goals",
                "extraction_timeout": "residual extraction exceeded its bounded deadline",
                "backend_error": "the residual extraction backend failed before returning structured state",
                "no_structured_state": "Lean exposed no reliable structured residual state",
            }
            unavailable = {"status": "unavailable", "failure_kind": failure_kind,
                           "reason": reasons[failure_kind], "detail": str(error)[:400], "cases": [],
                           "helper_stages": stages,
                           "backend_failure_phase": observed.get("failure_phase"),
                           "request_mode": request_mode,
                           "extraction_seconds": observed.get("seconds"),
                           "queue_wait_seconds": observed.get("queue_wait_seconds"),
                           "extraction_timeout_seconds": extraction_timeout,
                           "requested_extraction_timeout_seconds": extraction_timeout,
                           "admission_timeout_policy": arena.lean_timeout_scope(),
                           "diagnostics": [_diagnostic_preview(item)
                                           for item in sorted((item for item in observed.get("diagnostics", [])
                                                               if isinstance(item, dict)),
                                                              key=lambda item: item.get("severity") in {"warning", 2})[:2]]}
            if failure_kind == "extraction_timeout" and extraction_timeout < min(feedback.timeout, MAX_REQUEST_SECONDS):
                unavailable["retry_guidance"] = "Retry unfinished_cases explicitly with the same expected_sha256 and timeout_seconds=60; automatic failed-edit extraction remains capped at 15 seconds."
            atomic_text(path, json.dumps({"binding": binding, "generated_source_sha256": _sha(source.encode()),
                                          "unavailable": unavailable, "observation": observed}, ensure_ascii=False, indent=2) + "\n")
            return {**unavailable, "cache_hit": False, "details_path": str(path)}
        saved = {"binding": binding, "generated_source_sha256": _sha(source.encode()),
                 "record": record, "extraction_seconds": observed.get("seconds"),
                 "queue_wait_seconds": observed.get("queue_wait_seconds"),
                 "backend": observed.get("backend"), "extraction_timeout_seconds": extraction_timeout,
                 "helper_stages": stages}
        atomic_text(path, json.dumps(saved, ensure_ascii=False, indent=2) + "\n")
    if candidate.read_bytes() != raw or lean_goal_state.source_revision(candidate) != revision:
        return {"status": "source_conflict", "cases": [], "reason": "candidate changed during residual extraction"}
    payload_goals = []
    for case in record["cases"]:
        local_byte = case["position_byte"] - declaration_byte
        local_offset = len(snapshot.declaration.encode()[:local_byte].decode())
        position = lean_goal_state.offset_to_human_position(text, snapshot.declaration_start + local_offset)
        context = {"target": case["target"], "hypotheses": case["hypotheses"], "goal_index": case["index"]}
        count = sum(item["occurrence"] == case["occurrence"] for item in record["cases"])
        payload_goals.append({"target": case["target"], "case_name": case["case_name"],
                              "index": case["index"], "occurrence": case["occurrence"], "position": position,
                              "goal_count": count, "context": context, "record": _record_for_retrieval(case, count)})
    cases = []
    if payload_goals:
        handles = lean_goal_state.attach_goal_handles(feedback, snapshot_path, digest, {
            "goals": payload_goals, "phase": "residual", "source_revision": revision,
            "candidate_path": str(candidate.resolve()), "environment_fingerprint": binding["environment_fingerprint"],
            "position": {"candidate": payload_goals[0]["position"]}, "context_origin": "structured_unsolved_goal"})
        for case, handle in zip(payload_goals, handles["goal_handles"]):
            target = re.sub(r"\s+", " ", case["target"]).strip()
            cases.append({**handle, "case_name": str(handle.get("case_name", ""))[:120],
                          "target_preview": target[:240], "target_truncated": len(target) > 240,
                          "hypothesis_count": len(case["context"]["hypotheses"])})
    return {"status": record["status"], "cases": cases[:limit], "total_cases": record["total_cases"],
            "omitted": record["total_cases"] - len(cases[:limit]), "cache_hit": cache_hit,
            "phase": "residual", "details_path": str(path),
            "environment_fingerprint": binding["environment_fingerprint"],
            "prefix_sha256": prefix.sha256, "extraction_seconds": saved.get("extraction_seconds"),
            "queue_wait_seconds": saved.get("queue_wait_seconds"),
            "extraction_timeout_seconds": saved.get("extraction_timeout_seconds", extraction_timeout),
            "requested_extraction_timeout_seconds": extraction_timeout,
            "request_mode": request_mode,
            "helper_stages": saved.get("helper_stages", []),
            "admission_timeout_policy": arena.lean_timeout_scope()}


@bind_feedback_scoring_policy
def unfinished_cases(feedback: Any, request: dict[str, Any]) -> dict[str, Any]:
    started = time.perf_counter()
    result: dict[str, Any] = {"schema_version": 1, "tool": TOOL["name"], "authoritative": False,
                              "checkpoint": None, "cases": []}
    try:
        limit = _validate(request)
        candidate = feedback.candidate_path(request)
        raw = candidate.read_bytes()
        revision = lean_goal_state.source_revision(candidate)
        digest = _sha(raw)
        result.update(candidate=str(candidate), source_sha256=digest)
        if request["expected_sha256"] != digest:
            return {**result, "status": "source_conflict", "reason": "expected_sha256 does not match the current candidate"}
        snapshot_path = Path(getattr(feedback, "root", candidate.parent)) / ".feedback" / "sources" / f"{digest}.lean"
        from lean_tools.feedback_workflow import immutable_text
        immutable_text(snapshot_path, raw.decode("utf-8"))
        result["snapshot_path"] = str(snapshot_path)
        if "goal_id" in request:
            prefix = lean_source.exact_source_prefix(feedback.row, feedback.project)
            handle = lean_goal_state.resolve_goal_handle(feedback, candidate, digest, request["goal_id"], prefix.sha256)
            if handle.get("phase") != "residual":
                raise ValueError("goal_id is a historical entry goal; select a handle from unfinished_cases")
            binding = _binding(feedback, digest, prefix)
            if handle["environment_fingerprint"] != binding["environment_fingerprint"]:
                raise ValueError("goal_id belongs to a different Lean environment")
            result.update(status="ok", goal_id=request["goal_id"], phase="residual",
                          case_name=handle.get("case_name"), context=handle["context"],
                          goal=handle["goal"], occurrence=handle["occurrence"])
        else:
            result.update(_observe(feedback, candidate, raw, snapshot_path, limit,
                                   timeout_seconds=request.get("timeout_seconds", DEFAULT_REQUEST_SECONDS), request_mode="explicit"))
        # Also invalidate inspection results if a concurrent edit restored equal bytes.
        if candidate.read_bytes() != raw or lean_goal_state.source_revision(candidate) != revision:
            result.update(status="source_conflict", cases=[], reason="candidate changed during query")
            result.pop("context", None)
    except (ValueError, OSError, RuntimeError, KeyError, TypeError) as error:
        result.update(status="invalid_request" if "source_sha256" not in result or (isinstance(request, dict) and "goal_id" in request) else "unavailable",
                      reason=str(error)[:600], cases=[])
    result["seconds"] = round(time.perf_counter() - started, 6)
    return result


@bind_feedback_scoring_policy
def failure_feedback(feedback: Any, submission: Any, result: dict[str, Any], full: dict[str, Any]) -> dict[str, Any]:
    """At most one short best-effort extraction, only for an unsolved-goal failure."""
    evidence = [str(result.get("error", "")), str(full.get("lean_run", {}).get("output", ""))]
    evidence.extend(str(item.get("message", "")) for item in result.get("diagnostics", []) if isinstance(item, dict))
    if not any("unsolved goals" in value for value in evidence):
        return {"status": "unavailable", "failure_kind": "no_unsolved_goal_evidence", "cases": [], "reason": "failure has no structured unsolved-goal evidence; request unfinished_cases explicitly to inspect"}
    # The tool binds handles to the mutable draft, retaining the submitted snapshot
    # as the link. A concurrent edit must not receive advice for the old draft.
    if submission.candidate.read_bytes() != submission.source.encode("utf-8"):
        return {"status": "source_conflict", "cases": [], "reason": "candidate changed after the checked snapshot"}
    try:
        return _observe(feedback, submission.candidate, submission.source.encode("utf-8"), submission.path, DEFAULT_LIMIT)
    except (ValueError, OSError, RuntimeError, KeyError, TypeError) as error:
        return {"status": "unavailable", "cases": [], "reason": str(error)[:400]}

"""Per-run receipts for the validated unchanged original and score denominators."""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path

from lean_tools import arena_workflow as arena, lean_source
from .benchmark import digest, file_hash
from .config import runtime_source_hashes


def measurement_source_hashes() -> dict[str, str]:
    # Transport and model runtime repairs do not change an original measurement.
    # Pin the evaluator and its helper modules, plus the receipt/preflight boundary.
    return {path: value for path, value in runtime_source_hashes().items()
        if path.startswith("lean_tools/") or path in {
            "harness/baselines.py", "harness/doctor.py", "harness/environments.py"}}


def _positive(value, label):
    if type(value) is not int or value <= 0:
        raise ValueError(f"{label} must be a positive integer before model spending")
    return value


def _metadata_identity(metadata):
    return digest({key: value for key, value in metadata.items() if key != "baseline_receipt"})


def validate_original_evidence(metadata: dict, evidence: dict, *, quick: bool = False) -> None:
    """Admit complete native evidence, with no provisional scoring references."""
    if evidence.get("status") != "passed" or evidence.get("task_id") != metadata["task_id"]:
        raise ValueError("Original baseline evidence belongs to another task or did not pass")
    task = Path(metadata["task"])
    if file_hash(task) != metadata["task_sha256"]:
        raise ValueError("Original task changed during baseline preflight")
    document, row = arena.load_task(task)
    source = arena.render_candidate_scaffold(row)
    source_hash = arena.sha256_bytes(source.encode("utf-8"))
    if evidence.get("original_sha256") != source_hash:
        raise ValueError("Original baseline source hash differs from the unchanged original")
    if file_hash(Path(evidence["original_path"])) != source_hash:
        raise ValueError("Original baseline source evidence changed")
    if evidence.get("task_sha256") != metadata["task_sha256"]:
        raise ValueError("Original baseline task hash differs from preflight input")
    _, body = lean_source.extract_candidate_declaration(row,
        lean_source.candidate_text_from_bytes(source.encode("utf-8")))
    tokens = lean_source.candidate_proof_token_count(body, metadata.get("scoring_policy", "arena-v1"))
    if metadata["original_measurement_tokens"] != tokens:
        raise ValueError("Original token measurement differs from frozen convention")
    _positive(tokens, "Original measured tokens")
    _positive(metadata["original_tokens"], "Original token denominator")
    expected_tokens = row.get("proof_length", tokens)
    if metadata["original_tokens"] != expected_tokens:
        raise ValueError("Original token denominator differs from supplied proof_length or original token convention")
    projects = [metadata["primary"], *metadata["compatibility"]]
    environments = metadata["environments"]
    results = evidence.get("environments", [])
    if len(results) != len(projects) or len(environments) != len(projects):
        raise ValueError("Original baseline lacks complete compatibility evidence")
    for index, (project, expected, result) in enumerate(zip(projects, environments, results)):
        evaluation = result.get("evaluation", {})
        mode = "quick" if quick or index else "exact"
        if (expected["path"] != project or result.get("environment") != project
                or result.get("mode") != mode or result.get("valid") is not True
                or evaluation.get("valid") is not True
                or evaluation.get("task_id") != metadata["task_id"]
                or evaluation.get("source_sha256") != source_hash
                or evaluation.get("measurement_mode") != mode
                or evaluation.get("scoring_policy") != metadata.get("scoring_policy", "arena-v1")
                or evaluation.get("length", {}).get("candidate_tokens") != tokens
                or evaluation.get("length", {}).get("original_tokens") != metadata["original_tokens"]
                or evaluation.get("heartbeat", {}).get("environment_fingerprint") != expected["fingerprint"]):
            raise ValueError("Original baseline lacks valid source, environment, or token evidence")
        if file_hash(Path(result["evidence_path"])) != result.get("evidence_sha256"):
            raise ValueError("Original baseline evaluation evidence changed")
        if json.loads(Path(result["evidence_path"]).read_text()) != evaluation:
            raise ValueError("Original baseline evaluation differs from its evidence file")
        if mode == "exact":
            axioms = evaluation.get("axioms")
            if (evaluation.get("axiom_status") != "measured" or not isinstance(axioms, list)
                    or any(axiom not in arena.ALLOWED_AXIOMS for axiom in axioms)):
                raise ValueError("Original baseline lacks complete allowed-axiom evidence")
            _positive(evaluation.get("heartbeat", {}).get("candidate"), "Original measured heartbeats")
            if evaluation["heartbeat"].get("local_reference") != document.get("reference", {}).get("heartbeat"):
                raise ValueError("Original baseline used a different scoring reference")


def _resolved_evaluation(raw: dict, metadata: dict) -> dict:
    """Recalculate reference-dependent fields; retain every measured field verbatim."""
    value = deepcopy(raw)
    reference = metadata["original_heartbeats"]
    provenance = metadata["baseline_provenance"]["heartbeats"]["source"]
    heartbeat = value["heartbeat"]
    heartbeat.update(local_reference=reference,
        published_reference=reference if provenance == "supplied_heartbeat" else None,
        reference_source=provenance,
        note=("Reduction uses the supplied Arena heartbeat reference." if provenance == "supplied_heartbeat"
              else "Reduction uses the measured original heartbeat denominator."))
    measured = heartbeat["candidate"]
    heartbeat["reduction_pct"] = round(100 * (reference - measured) / reference, 2) if measured is not None else None
    value["local_two_axis_mean"] = (round((value["length"]["reduction_pct"] + heartbeat["reduction_pct"]) / 2, 4)
        if heartbeat["reduction_pct"] is not None else None)
    return value


def freeze_original_baseline(metadata: dict, evidence: dict, receipt_dir: Path) -> dict:
    """Freeze effective denominators and the checked original before any inference."""
    metadata = deepcopy(metadata)
    if metadata.get("baseline_receipt") is not None:
        raise ValueError("Original baseline is already frozen")
    validate_original_evidence(metadata, evidence)
    evaluated_task_sha256 = metadata["task_sha256"]
    measured = evidence["environments"][0]["evaluation"]["heartbeat"]["candidate"]
    supplied = metadata.get("original_heartbeats")
    document = json.loads(Path(metadata["task"]).read_text())
    if document.get("reference", {}).get("heartbeat") != supplied:
        raise ValueError("Original heartbeat metadata differs from the supplied task reference")
    if supplied is not None:
        _positive(supplied, "Supplied heartbeat denominator")
    denominator = supplied if supplied is not None else measured
    metadata["original_heartbeats"] = _positive(denominator, "Original heartbeat denominator")
    _, row = arena.load_task(Path(metadata["task"]))
    metadata["baseline_provenance"] = {
        "tokens": {"source": "supplied_proof_length" if "proof_length" in row else "measured_original_tokens",
                   "value": metadata["original_tokens"]},
        "heartbeats": {"source": "supplied_heartbeat" if supplied is not None else "measured_original_heartbeat",
                       "value": denominator}}
    document["reference"] = {**document.get("reference", {}), "heartbeat": denominator,
        "source": metadata["baseline_provenance"]["heartbeats"]["source"]}
    arena.write_json_atomic(Path(metadata["task"]), document)
    metadata["task_sha256"] = file_hash(Path(metadata["task"]))
    receipt = {"schema_version": 1, "kind": "per-run-original-baseline",
        "task_id": metadata["task_id"], "label": metadata["label"],
        "metadata_sha256": _metadata_identity(metadata),
        "evaluated_task_sha256": evaluated_task_sha256,
        "frozen_task_sha256": metadata["task_sha256"],
        "source_hashes": measurement_source_hashes(), "original_sha256": evidence["original_sha256"],
        "baseline_provenance": metadata["baseline_provenance"],
        "evidence": deepcopy(evidence),
        "evaluations": [_resolved_evaluation(item["evaluation"], metadata) for item in evidence["environments"]]}
    receipt_path = Path(receipt_dir).resolve() / f"{metadata['label']}.json"
    if receipt_path.exists():
        raise FileExistsError("Baseline receipt already exists; frozen evidence cannot be replaced")
    arena.write_json_atomic(receipt_path, receipt)
    metadata["baseline_receipt"] = {"path": str(receipt_path), "sha256": file_hash(receipt_path)}
    return metadata


def load_original_baseline(metadata: dict, *, verify_sources: bool = True,
        source_snapshot: dict | None = None) -> dict:
    """Validate per-run receipt integrity before reusing its native evaluations."""
    descriptor = metadata.get("baseline_receipt")
    if not isinstance(descriptor, dict):
        raise ValueError("Frozen proof lacks its per-run original baseline receipt")
    path = Path(descriptor["path"])
    if file_hash(path) != descriptor.get("sha256"):
        raise ValueError("Frozen original baseline receipt changed")
    receipt = json.loads(path.read_text())
    if (receipt.get("schema_version") != 1 or receipt.get("kind") != "per-run-original-baseline"
            or receipt.get("metadata_sha256") != _metadata_identity(metadata)
            or receipt.get("frozen_task_sha256") != metadata["task_sha256"]
            or file_hash(Path(metadata["task"])) != metadata["task_sha256"]
            or receipt.get("baseline_provenance") != metadata.get("baseline_provenance")):
        raise ValueError("Frozen original baseline receipt differs from proof metadata")
    if verify_sources and receipt.get("source_hashes") != measurement_source_hashes():
        if source_snapshot is None:
            raise ValueError("Original baseline measurement source or instrumentation changed")
        from .runtime_repair import verify_original_baseline_sources
        verify_original_baseline_sources(source_snapshot, metadata, receipt)
    evidence = receipt["evidence"]
    # Keep the measured task unchanged; only the effective reference is resolved later.
    evaluated_metadata = {**metadata, "task": evidence["task_path"],
        "task_sha256": receipt["evaluated_task_sha256"]}
    validate_original_evidence(evaluated_metadata, evidence)
    measured_document = json.loads(Path(evidence["task_path"]).read_text())
    measured_document["reference"] = {**measured_document.get("reference", {}),
        "heartbeat": metadata["original_heartbeats"],
        "source": metadata["baseline_provenance"]["heartbeats"]["source"]}
    if measured_document != json.loads(Path(metadata["task"]).read_text()):
        raise ValueError("Frozen task differs from measured original beyond its resolved reference")
    expected = [_resolved_evaluation(item["evaluation"], metadata) for item in evidence["environments"]]
    if expected != receipt.get("evaluations") or receipt.get("original_sha256") != evidence["original_sha256"]:
        raise ValueError("Frozen original baseline measurement evidence changed")
    _positive(metadata["original_tokens"], "Original token denominator")
    _positive(metadata["original_heartbeats"], "Original heartbeat denominator")
    return receipt

"""Contest JSONL export from frozen runs and independently revalidated incumbents."""
from __future__ import annotations

from decimal import Decimal
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

from lean_tools import arena_workflow as arena
from lean_tools.validation_policy import OriginalDenominatorScorePolicy
from .benchmark import file_hash
from .doctor import _native_environment


def _read(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"Expected object: {path}")
    return value


def _cost(snapshot: dict, item: dict, cell: Path) -> dict:
    from .openrouter.ledger import read_openrouter_receipt
    from .runner import proof_identity
    ledger = cell / "billing/openrouter.sqlite"
    if not ledger.exists():
        return {"status": "not_started", "actual_cost_usd": None, "ledger_present": False}
    receipt = read_openrouter_receipt(ledger)
    identity, budget = receipt["identity"], receipt["budget"]
    if (identity["proof_id"] != proof_identity(snapshot, item)
            or identity["model"] != snapshot["config"]["openrouter"]["model_id"]
            or Decimal(identity["limit_usd"]) != Decimal(snapshot["config"]["budget_usd"])):
        raise ValueError("Proof cost ledger belongs to a different run, row, model, or budget")
    cost_complete = not (budget["active_requests"] or budget["unknown_requests"])
    status = "settled" if cost_complete else "unresolved"
    if identity.get("breach_reason") or Decimal(budget["spent_usd"]) > Decimal(budget["limit_usd"]):
        status = "budget_breach"
    return {"status": status, "ledger_present": True, "receipt_sha256": receipt["sha256"],
        "identity": identity, "budget": budget,
        "actual_cost_usd": budget["spent_usd"] if cost_complete else None,
        "cost_reporting_complete": cost_complete,
        "over_budget_usd": str(max(Decimal(0), Decimal(budget["spent_usd"]) - Decimal(budget["limit_usd"]))),
        "reported_settled_cost_usd": budget["spent_usd"]}


def _evaluate_source(metadata: dict, source: str, directory: Path) -> dict:
    """Independent host evaluation; agent-written cache verdicts cannot bless export."""
    from e6.proof import _validation_infrastructure_failure
    directory.mkdir(parents=True, exist_ok=True)
    candidate = directory / "Candidate.lean"
    candidate.write_text(source, encoding="utf-8")
    environment = _native_environment(Path(metadata["elan_home"]), directory / "cache")
    results = []
    for index, project in enumerate([metadata["primary"], *metadata["compatibility"]]):
        output = directory / f"environment-{index:03d}.json"
        request = {"task": metadata["task"], "candidate": str(candidate), "project": project,
            "registry": metadata["registry_source"], "output": str(output),
            "scoring_policy": metadata.get("scoring_policy", "arena-v1"),
            "quick": index > 0, "timeout_seconds": 240}
        request_path = directory / f"environment-{index:03d}-request.json"
        request_path.write_text(json.dumps(request), encoding="utf-8")
        result = subprocess.run([sys.executable, "-m", "harness.doctor", "--worker", str(request_path)],
            cwd=Path(__file__).resolve().parents[1], env=environment,
            capture_output=True, text=True, timeout=270)
        if result.returncode or not output.is_file():
            raise ValueError(f"Independent Lean export validation failed: {(result.stderr or result.stdout)[-4000:]}")
        evaluation = _read(output)
        if _validation_infrastructure_failure(evaluation):
            raise ValueError(f"Independent Lean export validation infrastructure failure: {output}")
        results.append({"environment": project, "passed": bool(evaluation.get("valid")),
            "mode": "quick" if index else "exact", "evaluation": evaluation,
            "evidence_path": str(output), "evidence_sha256": file_hash(output)})
    primary = results[0]["evaluation"]
    if not results[0]["passed"]:
        raise ValueError("Export candidate failed exact primary validation")
    tokens = primary.get("length", {}).get("candidate_tokens")
    heartbeats = primary.get("heartbeat", {}).get("candidate")
    if type(tokens) is not int or tokens < 0 or type(heartbeats) is not int or heartbeats < 0:
        raise ValueError("Export candidate lacks exact token and heartbeat measurements")
    compatible = 100 * sum(item["passed"] for item in results) / len(results)
    policy = OriginalDenominatorScorePolicy(metadata["original_tokens"], metadata["original_heartbeats"],
        **({"scoring_policy": "arena-v1"} if metadata.get("scoring_policy") == "arena-v1" else {}))
    return {"tokens": tokens, "heartbeats": heartbeats, "compatibility_pct": compatible,
        "score": policy.score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=compatible),
        "environments": results}


def _best(snapshot: dict, item: dict, cell: Path) -> tuple[str, dict]:
    """Check checkpoint provenance and metadata before the independent Lean check."""
    from e6 import proof
    config = _read(cell / "config.json")
    proof._verify_config(config)
    if (config.get("product_run_identity") != snapshot["identity"]
            or config.get("product_metadata") != item
            or config.get("task_sha256") != item["task_sha256"]):
        raise ValueError("Incumbent configuration differs from the frozen run row")
    best = _read(cell / "best.json")
    checkpoint = Path(best.get("selected_path", "")).resolve()
    if not checkpoint.is_relative_to((cell / "verified").resolve()):
        raise ValueError("Incumbent must reference the private verified checkpoint directory")
    source = proof._source(checkpoint)
    proof._verify_incumbent(config, {**best, "source": source})
    if checkpoint.name != best["sha256"] + ".lean":
        raise ValueError("Verified checkpoint filename and source hash disagree")
    if best["sha256"] != config["initial_best"]["sha256"]:
        receipts = [p for p in (cell / "host-boundaries").glob("pass-*.json")]
        if not any((r := _read(path)).get("selected_sha256", r.get("best", {}).get("sha256")) == best["sha256"] for path in receipts):
            raise ValueError("Incumbent lacks a host validation or optimizer promotion receipt")
    return source, best


def _validate_run_proofs(snapshot: dict) -> None:
    names, environments = set(), {}
    for item in snapshot["proofs"]:
        if item["task_id"] in names:
            raise ValueError(f"Repeated proof in frozen run: {item['task_id']}")
        names.add(item["task_id"])
        for environment in item.get("environments", []):
            sid = environment["snapshot_id"]
            identity = {key: environment.get(key) for key in (
                "path", "repository", "revision", "snapshot_requirement_sha256")}
            if sid in environments and environments[sid] != identity:
                raise ValueError(f"Frozen run has changed snapshot identity: {sid}")
            environments[sid] = identity


def export_run(root: str | Path, output: str | Path, *, verify: bool = True) -> dict:
    """Write full name/proof declarations, retaining an independently checked original fallback.

    Cost uncertainty is reported as unresolved liability. It never becomes a zero
    charge, and does not discard a previously verified mathematical incumbent.
    """
    from .runner import load_snapshot, proof_root, run_lock
    if not verify:
        raise ValueError("Submission export always requires independent host verification")
    if not isinstance(root, (str, Path)):
        raise ValueError("Export requires one frozen run directory")
    root = Path(root).resolve()
    output = Path(output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    evidence = output.parent / (output.name + ".evidence")
    if evidence.exists():
        raise FileExistsError(f"Fresh export evidence directory required: {evidence}")
    report = {"schema_version": 1, "status": "validating", "roots": [str(root)],
        "output": str(output), "proofs": [], "failures": [], "paid_inference": False}
    started = time.monotonic()
    rows = []
    try:
        with run_lock(root):
            snapshot = load_snapshot(root)
            _validate_run_proofs(snapshot)
            report["run_identities"] = [snapshot["identity"]]
            from .runtime_repair import summary as runtime_summary
            report["runtime_revisions"] = [runtime_summary(snapshot)]
            evidence.mkdir()
            for item in snapshot["proofs"]:
                cell = proof_root(root, item)
                if file_hash(Path(item["task"])) != item["task_sha256"]:
                    raise ValueError(f"Frozen original task changed: {item['task_id']}")
                _, row = arena.load_task(Path(item["task"]))
                detail = {"name": row["name"], "label": item["label"], "run_identity": snapshot["identity"],
                    "row_sha256": item.get("row_sha256"), "environment_map_identity": item.get("environment_map_identity")}
                cost_valid = True
                try:
                    detail["cost"] = _cost(snapshot, item, cell)
                except Exception as error:
                    cost_valid = False
                    detail["cost"] = {"status": "invalid", "error": str(error), "actual_cost_usd": None}
                    report["failures"].append({"name": row["name"], "stage": "cost", "error": str(error)})
                directory = evidence / item["label"]
                incumbent_error = None
                source, best = None, None
                if (cell / "best.json").is_file() and cost_valid:
                    try:
                        source, best = _best(snapshot, item, cell)
                        original_source = arena.render_candidate_scaffold(row)
                        if source != original_source and not detail["cost"]["ledger_present"]:
                            raise ValueError("Improved incumbent has no immutable proof cost ledger")
                        validation = _evaluate_source(item, source, directory / "incumbent")
                        for key in ("tokens", "heartbeats", "compatibility_pct", "score"):
                            if best.get(key) != validation[key]:
                                raise ValueError(f"Incumbent {key} disagrees with independent export validation")
                        detail.update(selection="verified_incumbent", validation=validation)
                    except Exception as error:
                        incumbent_error, source = str(error), None
                if source is None:
                    source = arena.render_candidate_scaffold(row)
                    try:
                        validation = _evaluate_source(item, source, directory / "original")
                    except Exception as error:
                        detail.update(selection="failed", error=str(error), incumbent_error=incumbent_error)
                        report["proofs"].append(detail)
                        raise ValueError(f"No validated original fallback for {row['name']}: {error}") from error
                    detail.update(selection="original_fallback", validation=validation,
                        fallback_reason=incumbent_error or "proof_not_started_or_no_valid_incumbent")
                    if incumbent_error:
                        report["failures"].append({"name": row["name"], "stage": "incumbent", "error": incumbent_error})
                declaration, _ = arena.extract_candidate_declaration(row, source)
                detail.update(source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                    declaration_sha256=hashlib.sha256(declaration.encode()).hexdigest())
                rows.append({"name": row["name"], "proof": declaration})
                report["proofs"].append(detail)
            temporary = output.with_name(output.name + ".tmp")
            temporary.write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows), encoding="utf-8")
            temporary.replace(output)
            report.update(status="exported_with_failures" if report["failures"] else "exported",
                row_count=len(rows), output_sha256=file_hash(output),
                cost_status=("unresolved" if any(p["cost"]["status"] in {"unresolved", "invalid"}
                    or (p["cost"]["status"] == "budget_breach" and p["cost"].get("actual_cost_usd") is None) for p in report["proofs"])
                    else "budget_breach" if any(p["cost"]["status"] == "budget_breach" for p in report["proofs"])
                    else "settled_or_not_started"))
    except Exception as error:
        report.update(status="failed", error_type=type(error).__name__, error=str(error))
        report["failures"].append({"stage": "export", "error": str(error)})
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        report_path = output.with_name(output.name + ".report.json")
        report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    report["report_path"] = str(report_path)
    return report

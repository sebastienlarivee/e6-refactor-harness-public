#!/usr/bin/env python3
"""Read saved product run snapshots; never import or modify the runner."""
from __future__ import annotations

import argparse
from decimal import Decimal, InvalidOperation
import hashlib
import json
from pathlib import Path
import shlex


def read(path):
    try:
        value = json.loads(path.read_text(encoding="utf-8-sig"))
        return value if isinstance(value, dict) else {}
    except (OSError, ValueError):
        return {}


def original_proof_progress(root):
    """Count completed original receipts for the resolved proof selection."""
    proofs = read(root / "benchmark/benchmark.json").get("proofs")
    if not isinstance(proofs, list) or not proofs:
        return None

    completed = 0
    labels = set()
    for proof in proofs:
        label = proof.get("label") if isinstance(proof, dict) else None
        if (not isinstance(label, str) or not label or label in labels
                or "/" in label or "\\" in label):
            return None
        labels.add(label)
        receipt = read(root / "baselines" / f"{label}.json")
        evidence = receipt.get("evidence")
        if (receipt.get("kind") == "per-run-original-baseline" and receipt.get("label") == label
                and receipt.get("task_id") == proof.get("task_id")
                and isinstance(evidence, dict) and evidence.get("status") == "passed"):
            completed += 1
    return completed, len(proofs)


def decimal(value):
    try:
        result = Decimal(str(value))
        return result if result.is_finite() else None
    except (InvalidOperation, TypeError, ValueError):
        return None


def money(value):
    number = decimal(value)
    return f"{number:.4f}" if number is not None else "-"


def elapsed(value):
    number = decimal(value)
    if number is None or number < 0:
        return "-"
    seconds = int(number)
    return f"{seconds // 3600:02d}:{seconds // 60 % 60:02d}:{seconds % 60:02d}"


def status_label(value):
    return {
        "preparing_pass": "preparing",
        "validating_pass": "verifying",
        "optimizing_pass": "optimizing",
        "settling_pending_usage": "settling usage",
        "screening_next_attempt": "screening",
        "waiting_broker_startup": "waiting for broker",
        "starting_broker": "starting broker",
        "budget_reached": "budget reached",
        "diagnostic_pass_cap": "pass cap reached",
        "host_requested_stop": "host stopped",
    }.get(value, str(value).replace("_", " "))


def model_label(value):
    name = str(value).rsplit("/", 1)[-1]
    if name.startswith("gpt-"):
        return "GPT-" + " ".join(part.capitalize() for part in name[4:].split("-"))
    return name


def export_retry_command(root, *, release_root=None):
    """Choose unused evidence and artifact paths without changing any files."""
    root = Path(root)
    release_root = Path(release_root or Path(__file__).resolve().parents[1])
    number = 1
    while True:
        suffix = "" if number == 1 else f"-{number}"
        output = root / f"submission-retry{suffix}.jsonl"
        if not any(Path(str(output) + tail).exists() for tail in ("", ".evidence", ".report.json", ".tmp")):
            break
        number += 1
    return shlex.join([str(release_root / ".venv/bin/harness"), "export", str(root), "--output", str(output)])


def process_start_tick(pid):
    """Read Linux process identity without signaling or importing the runner."""
    if type(pid) is not int or pid <= 0:
        return None
    try:
        value = (Path("/proc") / str(pid) / "stat").read_text()
        return int(value[value.rindex(")") + 2:].split()[19])
    except (OSError, ValueError, IndexError):
        return None


def submission_status(root, snapshot, state):
    """Distinguish finished proof work from a verified, available export."""
    if state.get("status") != "completed":
        return status_label(state.get("status", "unknown")), []
    publication = read(root / "submission-status.json")
    if publication.get("run_identity") != snapshot.get("identity"):
        publication = {}
    failed, incomplete = [], []
    # A manual inference-free export may use a fresh filename after a failure.
    # Recognize it through its run identity and the exact artifact hash.
    for report_path in sorted(root.glob("*.jsonl.report.json")):
        report = read(report_path)
        if report.get("roots") != [str(root)]:
            continue
        output = Path(str(report_path)[:-len(".report.json")])
        if report.get("status") == "failed":
            failed.append((report_path, report))
            continue
        if (report.get("status") not in {"exported", "exported_with_failures"}
                or report.get("run_identities") != [snapshot.get("identity")]
                or report.get("output") != str(output)):
            continue
        try:
            valid = hashlib.sha256(output.read_bytes()).hexdigest() == report.get("output_sha256")
        except OSError:
            valid = False
        if not valid:
            incomplete.append(f"Export artifact is missing or differs from its report: {output}")
            continue
        messages = [f"Submission: {output}", f"Export report: {report_path}"]
        if report.get("failures"):
            messages.append("Export has reported failures; review original fallbacks in the report")
        if report.get("cost_status") in {"unresolved", "budget_breach"}:
            messages.append(f"Export cost status: {status_label(report['cost_status'])}; review the report")
        return "submission ready", messages
    live = (publication.get("status") == "exporting"
            and publication.get("process_start_tick") is not None
            and process_start_tick(publication.get("pid")) == publication["process_start_tick"])
    if live:
        return "exporting", [f"Export target: {root / 'submission.jsonl'}"]
    if publication.get("status") in {"exporting", "export_interrupted"}:
        label = "export interrupted"
    elif publication.get("status") == "export_failed" or failed:
        label = "export failed"
    elif incomplete:
        label = "export incomplete"
    else:
        label = "proofs completed; export pending"
    messages = list(incomplete)
    if publication.get("error"):
        messages.append(f"Export: {publication['error']}")
    elif failed:
        report_path, report = failed[-1]
        messages.extend([f"Export: {report.get('error', 'validation failed')}", f"Export report: {report_path}"])
    messages.append(f"Retry export without inference: {export_retry_command(root)}")
    return label, messages


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True, type=Path)
    root = parser.parse_args(argv).root.expanduser().resolve()
    snapshot = read(root / "resolved-config.json")
    if not snapshot:
        doctor = read(root / "doctor.json") or read(root / "doctor/doctor.json")
        print(f"{'Preflight failed' if doctor.get('status') == 'failed' else 'No frozen run snapshot yet'}: {root}")
        progress = original_proof_progress(root)
        if progress is not None:
            completed, total = progress
            print(f"Original proofs checked: {completed}/{total}")
        print("Preflight must finish before inference starts. Inspect the launcher log and doctor evidence.")
        print("If the launcher has stopped, preserve this directory and choose a fresh --output directory; --resume is unavailable.")
        return 1
    config = snapshot.get("config", {})
    state = read(root / "state.json")
    rows, issues = [], []
    names = {}
    spent = Decimal(0)
    incomplete_spend = False
    overrun = Decimal(0)
    for metadata in snapshot.get("proofs", []):
        label = metadata["label"]
        name = names[label] = metadata.get("task_id", label)
        cell = root / "proofs" / label
        proof = read(cell / "state.json")
        best = read(cell / "best.json")
        billing = read(cell / "billing/status.json") or proof.get("budget") or {}
        status = proof.get("status", "pending")
        amount = decimal(billing.get("spent_usd"))
        limit = decimal(billing.get("limit_usd"))
        if amount is not None:
            spent += amount
            if limit is not None:
                overrun += max(Decimal(0), amount - limit)
        else:
            incomplete_spend = True
            if status not in {"pending", "preparing", "prepared", "starting"}:
                issues.append(f"{name}: spend unavailable")
        unknown_count = billing.get("unknown_requests")
        if type(unknown_count) is int and unknown_count > 0:
            incomplete_spend = True
            issues.append(f"{name}: {unknown_count} missing cost receipt{'s' if unknown_count != 1 else ''}")
        elif (billing.get("cost_reporting_complete") is False
              or (type(unknown_count) is not int and billing.get("cost_reporting_complete") is not True)):
            incomplete_spend = True
            if amount is not None:
                issues.append(f"{name}: cost reporting incomplete")
        score = best.get("score") if best.get("valid") is True and best.get("compatibility_complete") is True else None
        attempts = proof.get("passes", [])
        failed = sum(row.get("agent_status") == "failed"
                     or row.get("native_status") == "failed" for row in attempts)
        interrupted = sum(row.get("agent_status") == "interrupted"
                          or row.get("native_status") == "interrupted" for row in attempts)
        validation_failed = sum(row.get("validation_healthy") is False for row in attempts)
        problems = []
        if failed:
            problems.append(f"{failed} failed pass{'es' if failed != 1 else ''}")
        if interrupted:
            problems.append(f"{interrupted} interrupted pass{'es' if interrupted != 1 else ''}")
        if validation_failed:
            problems.append(f"{validation_failed} validation failure{'s' if validation_failed != 1 else ''}")
        if problems:
            issues.append(f"{name}: {', '.join(problems)}")
        rows.append((name, status_label(status), str(proof.get("pass_number", "-")),
                     money(amount), money(score)))
    model = config.get("openrouter", {})
    effort = model.get("default_reasoning_effort")
    title = model_label(model.get("model_id", "Unknown model"))
    if effort:
        title += f" / {effort}"
    phase, export_messages = submission_status(root, snapshot, state)
    print(f"{title}  |  {phase}"
          f"  |  elapsed {elapsed(state.get('elapsed_seconds'))}")
    print()
    headers = ("Theorem", "Status", "Pass", "Spent $", "Best score")
    widths = [max([len(header), *(len(row[index]) for row in rows)])
              for index, header in enumerate(headers)]

    def table_row(values):
        return "  ".join(f"{value:<{width}}" if index < 2 else f"{value:>{width}}"
                         for index, (value, width) in enumerate(zip(values, widths)))

    print(table_row(headers))
    print("  ".join("-" * width for width in widths))
    for row in rows:
        print(table_row(row))
    budget = decimal(config.get("budget_usd"))
    total_budget = budget * len(rows) if budget is not None else None
    total = f"${spent:.4f}"
    if total_budget is not None:
        total += f" / ${total_budget:.2f}"
    print(f"\n{'Known spend' if incomplete_spend else 'Total'}: {total}")
    if overrun:
        excess = f"${overrun:.4f}" if overrun >= Decimal("0.00005") else "<$0.0001"
        issues.append(f"Settled charges above proof limits: {excess}")
    for label, code in state.get("worker_returncodes", {}).items():
        if code:
            issues.append(f"{names.get(label, label)}: worker exited with code {code}")
    if state.get("recovery_error"):
        issues.append(state["recovery_error"].get("message", "Automatic recovery needs attention"))
    for issue in issues:
        print(f"! {issue}")
    for message in export_messages:
        print(message)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

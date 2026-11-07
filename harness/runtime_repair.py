"""Explicit host-authorized runtime repairs without resetting run or budget identity.

Normal run/resume never creates a repair. The operator must call authorize()
after reviewing a code fix. Original frozen configuration and proof ledgers are
untouched; an append-only receipt pins the complete replacement runtime.
"""
from contextlib import ExitStack
from pathlib import Path
import json

from .config import digest, file_hash, runtime_source_hashes, verify_source_hashes

BASELINE_POLICY = "preserve-reviewed-original-measurements-v1"


def _measurement_sources(sources):
    # Keep the same measurement boundary as baselines.measurement_source_hashes.
    return {path: value for path, value in sources.items()
            if path.startswith("lean_tools/") or path in {
                "harness/baselines.py", "harness/doctor.py", "harness/environments.py"}}


def _verify_preserved_baselines(snapshot, receipt, prior_revisions):
    preserved = receipt.get("preserved_original_baselines")
    if preserved is None:
        return
    items = {item["label"]: item for item in snapshot["proofs"]
             if item.get("baseline_receipt") is not None}
    if (not isinstance(preserved, dict) or preserved.get("policy") != BASELINE_POLICY
            or preserved.get("target_measurement_sources") != _measurement_sources(receipt["source_hashes"])
            or not isinstance(preserved.get("proofs"), dict)
            or set(preserved["proofs"]) != set(items) or not items):
        raise RuntimeError("Runtime repair original baseline preservation binding changed")
    recorded = [_measurement_sources(sources) for sources in prior_revisions]
    for label, item in items.items():
        entry = preserved["proofs"][label]
        if (not isinstance(entry, dict) or entry.get("metadata_sha256") != digest(item)
                or entry.get("baseline_receipt") != item["baseline_receipt"]
                or entry.get("measurement_sources") not in recorded):
            raise RuntimeError("Runtime repair original baseline preservation binding changed")


def history(snapshot):
    root = Path(snapshot["root"])
    directory = root / "runtime-repairs"
    revisions, receipts = [snapshot.get("source_hashes", {})], []
    if directory.is_symlink():
        raise RuntimeError("Runtime repair directory must not be a symlink")
    if not directory.exists():
        return revisions, receipts
    paths = sorted(directory.iterdir())
    for number, path in enumerate(paths, 1):
        if path.name != f"{number:03d}.json" or path.is_symlink() or not path.is_file():
            raise RuntimeError("Invalid runtime repair sequence")
        receipt = json.loads(path.read_text())
        payload = {k: v for k, v in receipt.items() if k != "receipt_sha256"}
        if (receipt.get("schema_version") != 1 or receipt.get("receipt_sha256") != digest(payload)
                or receipt.get("run_identity") != snapshot["identity"]
                or receipt.get("previous_sources_sha256") != digest(revisions[-1])
                or not isinstance(receipt.get("reason"), str) or not receipt["reason"].strip()
                or not isinstance(receipt.get("source_hashes"), dict)
                or receipt.get("sources_sha256") != digest(receipt["source_hashes"])):
            raise RuntimeError("Runtime repair receipt or binding changed")
        _verify_preserved_baselines(snapshot, receipt, revisions)
        revisions.append(receipt["source_hashes"])
        receipts.append(receipt)
    return revisions, receipts


def effective_sources(snapshot):
    return history(snapshot)[0][-1]


def _baseline_sources_authorized(snapshot, metadata, baseline, current_sources):
    _, receipts = history(snapshot)
    for receipt in reversed(receipts):
        preserved = receipt.get("preserved_original_baselines", {})
        if preserved.get("target_measurement_sources") != current_sources:
            continue
        entry = preserved.get("proofs", {}).get(metadata["label"], {})
        if (entry.get("metadata_sha256") == digest(metadata)
                and entry.get("baseline_receipt") == metadata.get("baseline_receipt")
                and entry.get("measurement_sources") == baseline.get("source_hashes")):
            return True
    return False


def verify_original_baseline_sources(snapshot, metadata, baseline):
    """Permit unchanged original evidence only through its explicit run repair.

    This never replaces a denominator or a native verdict. The normal baseline
    loader still verifies every original/task/evaluation byte and identity.
    Later measurement changes require another explicit preservation review.
    """
    from .baselines import measurement_source_hashes
    path = Path(snapshot.get("root", "")) / "resolved-config.json"
    if (snapshot.get("identity") != digest({k: v for k, v in snapshot.items() if k != "identity"})
            or not path.is_file() or json.loads(path.read_text()) != snapshot
            or metadata not in snapshot.get("proofs", [])):
        raise ValueError("Original baseline source authority differs from its frozen run")
    if not _baseline_sources_authorized(snapshot, metadata, baseline, measurement_source_hashes()):
        raise ValueError("Original baseline measurement source change lacks explicit preservation authorization")


def verify_prepared_sources(config, snapshot):
    """Accept prepared proof code only from a recorded revision of this run."""
    from e6.config import REPO_ROOT
    revisions, receipts = history(snapshot)
    if not receipts:
        for path, expected in config["source_hashes"].items():
            if file_hash(Path(path)) != expected:
                raise RuntimeError(f"Prepared runner changed: {path}")
        return
    try:
        prepared = {str(Path(path).relative_to(REPO_ROOT)): value
                    for path, value in config["source_hashes"].items()}
    except ValueError as error:
        raise RuntimeError("Prepared runner source is outside the runtime") from error
    if prepared not in revisions:
        raise RuntimeError("Prepared runner is not a recorded runtime revision")
    verify_source_hashes(revisions[-1])


def summary(snapshot):
    revisions, receipts = history(snapshot)
    return {"run_identity": snapshot["identity"], "original_sources_sha256": digest(revisions[0]),
            "effective_sources_sha256": digest(revisions[-1]),
            "repairs": [{**{k: r[k] for k in ("receipt_sha256", "reason", "created_at",
                "previous_sources_sha256", "sources_sha256", "changed_paths", "proof_states")},
                **({"preserved_original_baseline_count": len(r["preserved_original_baselines"]["proofs"])}
                     if "preserved_original_baselines" in r else {})}
                for r in receipts]}


def authorize(root, *, reason, preserve_original_baselines=False):
    """Host action: pin current code while every run/proof execution lock is free."""
    from . import runner
    from lean_tools.arena_workflow import utc_now
    if not isinstance(reason, str) or not reason.strip():
        raise ValueError("A concrete runtime repair reason is required")
    if type(preserve_original_baselines) is not bool:
        raise ValueError("Original baseline preservation requires an explicit boolean")
    root = Path(root).resolve()
    with ExitStack() as locks:
        locks.enter_context(runner.run_lock(root))
        snapshot = runner.load_snapshot(root, verify=False)
        for item in snapshot["proofs"]:
            cell = runner.proof_root(root, item)
            if cell.exists():
                locks.enter_context(runner.run_lock(cell))
        revisions, receipts = history(snapshot)
        current = runtime_source_hashes()
        if current == revisions[-1]:
            raise RuntimeError("No runtime change requires authorization")
        # Runtime authorization cannot waive input/environment integrity checks.
        for entry in snapshot["input_hashes"].values():
            if file_hash(Path(entry["path"])) != entry["sha256"]:
                raise RuntimeError("Frozen input changed before runtime repair")
        from .environments import verify_resolved_metadata
        from .baselines import load_original_baseline
        preserved = {}
        target_measurement_sources = _measurement_sources(current)
        for item in snapshot["proofs"]:
            verify_resolved_metadata(item)
            if file_hash(Path(item["task"])) != item["task_sha256"]:
                raise RuntimeError("Frozen proof row changed before runtime repair")
            if item.get("baseline_receipt") is None:
                if preserve_original_baselines:
                    raise ValueError("Explicit original preservation requires every proof's frozen baseline receipt")
                continue
            baseline = load_original_baseline(item, verify_sources=False)
            stored_sources = baseline.get("source_hashes")
            if preserve_original_baselines:
                if stored_sources not in [_measurement_sources(sources) for sources in revisions]:
                    raise ValueError("Original baseline sources are not a recorded runtime revision")
                preserved[item["label"]] = {"metadata_sha256": digest(item),
                    "baseline_receipt": item["baseline_receipt"], "measurement_sources": stored_sources}
            elif (stored_sources != target_measurement_sources
                    and not _baseline_sources_authorized(snapshot, item, baseline, target_measurement_sources)):
                raise ValueError("Measurement changes require explicit preserve_original_baselines=True after review")
        before = revisions[-1]
        changed = sorted(k for k in set(before) | set(current) if before.get(k) != current.get(k))
        states = {}
        for item in snapshot["proofs"]:
            cell = runner.proof_root(root, item)
            state = runner.read(cell / "state.json") if (cell / "state.json").exists() else {}
            states[item["label"]] = {"status": state.get("status", "prepared"),
                "pass_number": state.get("pass_number"), "proof_budget_identity": runner.proof_identity(snapshot, item)}
        payload = {"schema_version": 1, "run_identity": snapshot["identity"],
            "reason": reason.strip(), "created_at": utc_now(),
            "previous_sources_sha256": digest(before), "sources_sha256": digest(current),
            "source_hashes": current, "changed_paths": changed, "proof_states": states}
        if preserve_original_baselines:
            if not preserved:
                raise ValueError("No frozen original baselines are available to preserve")
            payload["preserved_original_baselines"] = {"policy": BASELINE_POLICY,
                "target_measurement_sources": target_measurement_sources, "proofs": preserved}
        receipt = {**payload, "receipt_sha256": digest(payload)}
        directory = root / "runtime-repairs"
        directory.mkdir(exist_ok=True)
        path = directory / f"{len(receipts) + 1:03d}.json"
        with path.open("x") as destination:
            destination.write(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
        return summary(snapshot)

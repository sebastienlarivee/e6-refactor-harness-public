"""Bounded host recovery at an idle run boundary; never dispatches inference.

Generation receipts are authoritative. Exclusive-key reconciliation can only
authorize one provisional zero-cost assumption; it never invents a provider bill.
"""
from __future__ import annotations

from contextlib import ExitStack, contextmanager
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
import hashlib
import json
import os
from pathlib import Path
import time

from .config import digest, file_hash
from .openrouter.keys import InferenceKeyFile
from .openrouter.ledger import OpenRouterLedger, read_openrouter_receipt, receipt_identity, _sum


RECOVERABLE = {"unknown_usage", "unreconciled_provider_cost", "upstream_http_error", "upstream_error"}
COOLDOWN_SECONDS = 300
AUDIT_INTERVAL_SECONDS = 30


def _read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)
    fd = os.open(path.parent, os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _money(value):
    if isinstance(value, bool) or not isinstance(value, (str, int, float, Decimal)):
        raise ValueError("Missing or invalid key usage counter")
    try:
        amount = Decimal(str(value))
    except InvalidOperation:
        raise ValueError("Missing or invalid key usage counter") from None
    if not amount.is_finite() or amount < 0:
        raise ValueError("Missing or invalid key usage counter")
    return amount


class RecoveryCoordinator:
    """Caller owns the root runner lock; all recovery happens without live cells."""

    def __init__(self, root, snapshot, *, api_key_file, key_client=None,
                 relay_factory=None, sleep=time.sleep, clock=time.time,
                 cooldown_seconds=COOLDOWN_SECONDS, audit_interval=AUDIT_INTERVAL_SECONDS):
        self.root = Path(root)
        self.snapshot = snapshot
        self.policy = snapshot["config"].get("recovery_policy", "none")
        self.directory = self.root / "recovery"
        self.path = self.directory / "state.json"
        self.key_client = key_client or InferenceKeyFile(api_key_file)
        self.relay_factory = relay_factory
        self.sleep, self.clock = sleep, clock
        self.cooldown_seconds, self.audit_interval = cooldown_seconds, audit_interval
        self.state = None

    def _now(self):
        return datetime.fromtimestamp(self.clock(), timezone.utc).isoformat()

    def _credential(self):
        key = self.key_client.credential()
        fingerprint = hashlib.sha256(key.encode()).hexdigest()
        bound = _read(self.root / "credential-identity.json")
        if bound.get("run_identity") != self.snapshot["identity"] or bound.get("key_sha256") != fingerprint:
            raise RuntimeError("Recovery credential differs from the frozen run binding")
        return key, fingerprint

    def _save(self):
        _write(self.path, self.state)

    def _evidence(self, kind, value):
        number = self.state.get("evidence_count", 0) + 1
        target = self.directory / f"{number:04d}-{kind}.json"
        # A crash after evidence publication must not overwrite its history.
        while target.exists():
            number += 1
            target = self.directory / f"{number:04d}-{kind}.json"
        _write(target, {"at": self._now(), "run_identity": self.snapshot["identity"], **value})
        self.state["evidence_count"] = number
        self._save()
        return target

    def _key_totals(self):
        key, fingerprint = self._credential()
        data = self.key_client.transport.call("GET", "/key", key).get("data")
        if not isinstance(data, dict):
            raise ValueError("Recovery requires ordinary key usage metadata")
        for field in ("is_management_key", "is_provisioning_key", "disabled"):
            if field in data and data[field] is not False:
                raise ValueError("Recovery requires an available ordinary inference key")
        # Require both counters rather than assuming missing BYOK liability is zero.
        return {"key_sha256": fingerprint, "usage": str(_money(data.get("usage"))),
                "byok_usage": str(_money(data.get("byok_usage")))}

    def _collect(self):
        from .runner import proof_identity
        receipts = {}
        for item in self.snapshot["proofs"]:
            path = self.root / "proofs" / item["label"] / "billing/openrouter.sqlite"
            if not path.exists():
                continue
            receipt = read_openrouter_receipt(path)
            identity = receipt["identity"]
            if (identity["proof_id"] != proof_identity(self.snapshot, item)
                    or identity["model"] != self.snapshot["config"]["openrouter"]["model_id"]
                    or Decimal(identity["limit_usd"]) != Decimal(self.snapshot["config"]["budget_usd"])):
                raise RuntimeError("Recovery found a foreign proof ledger")
            receipts[item["label"]] = receipt
        return receipts

    @contextmanager
    def _quiescent(self):
        from .runner import run_lock
        from e6.resume import assert_processes_gone
        with ExitStack() as stack:
            for item in self.snapshot["proofs"]:
                cell = self.root / "proofs" / item["label"]
                if not cell.exists():
                    continue
                stack.enter_context(run_lock(cell))
                if (cell / "state.json").exists():
                    assert_processes_gone(cell, _read(cell / "state.json"))
            yield

    def initialize(self):
        if self.policy not in {"generation-v1", "exclusive-key-v1"}:
            raise ValueError("Recovery coordinator requires a frozen recovery policy")
        _, fingerprint = self._credential()
        expected = {"schema_version": 1, "run_identity": self.snapshot["identity"],
                    "key_sha256": fingerprint, "policy": self.policy}
        if self.path.exists():
            self.state = _read(self.path)
            if any(self.state.get(k) != v for k, v in expected.items()):
                raise RuntimeError("Recovery policy or credential binding changed")
            if not isinstance(self.state.get("requeued"), dict):
                raise RuntimeError("Invalid durable recovery retry record")
            if self.state.get("presumption"):
                with self._quiescent():
                    self._check_presumption(self._collect())
            return
        self.state = {**expected, "started_at": self._now(), "requeued": {},
                      "baseline": None, "presumption": None, "evidence_count": 0}
        if self.policy == "exclusive-key-v1":
            with self._quiescent():
                existing = self._collect()
                if any(receipt["requests"] for receipt in existing.values()):
                    # Never reconstruct an unobserved starting balance on resume.
                    self.state["baseline_unavailable"] = True
                else:
                    self.state["baseline"] = {"at": self._now(), **self._key_totals()}
        self._save()

    @staticmethod
    def _totals(receipts):
        return {"usage": _sum([Decimal(r["budget"]["openrouter_cost_usd"]) for r in receipts.values()]),
                "byok_usage": _sum([Decimal(r["budget"]["byok_upstream_cost_usd"]) for r in receipts.values()])}

    def _stable_audit(self, receipts):
        baseline = self.state.get("baseline")
        if baseline is None:
            return False, None
        known = self._totals(receipts)
        pins = {label: r["sha256"] for label, r in receipts.items()}
        samples = []
        for index in range(3):
            if index:
                self.sleep(self.audit_interval)
            samples.append({"at": self._now(), **self._key_totals()})
        current = self._collect()
        unchanged = pins == {label: r["sha256"] for label, r in current.items()}
        matched = unchanged and all(
            Decimal(sample[field]) == _sum([Decimal(baseline[field]), known[field]])
            for sample in samples for field in ("usage", "byok_usage"))
        evidence = self._evidence("key-audit", {
            "baseline": baseline, "known_charges": {k: str(v) for k, v in known.items()},
            "ledger_sha256": pins, "samples": samples, "ledger_unchanged": unchanged,
            "matched": matched, "authority": "exclusive_key_provisional_inference",
            "delayed_charge_remains_possible": True})
        return matched, evidence

    def _ledger(self, receipt):
        identity = receipt["identity"]
        return OpenRouterLedger(receipt["ledger_path"], proof_id=identity["proof_id"],
                                model=identity["model"], limit_usd=identity["limit_usd"])

    def _publish_budget(self, label, *, revoked=False):
        """Refresh host status after a ledger-only recovery; candidates stay intact."""
        cell = self.root / "proofs" / label
        receipt = read_openrouter_receipt(cell / "billing/openrouter.sqlite")
        path = cell / "billing/status.json"
        budget = {**(_read(path) if path.exists() else {}), **receipt["budget"]}
        budget.update(cost_reporting_complete=not budget["unknown_requests"], closed=True,
            over_budget_usd=str(max(Decimal(0), _sum([Decimal(budget["spent_usd"]), Decimal(budget["limit_usd"]).copy_negate()]))))
        if budget["halted_reason"]:
            budget["stop_reason"] = budget["halted_reason"]
        else:
            budget["stop_reason"] = None
            budget["budget_failure_code"] = None
            budget["last_error"] = None
        _write(path, budget)
        if (cell / "state.json").exists():
            state = _read(cell / "state.json")
            state["budget"] = budget
            if revoked:
                state.update(status="unknown_usage", stop_reason="Provisional recovery revoked after key usage discrepancy")
            elif (not budget["active_requests"] and Decimal(budget["remaining_usd"]) <= 0
                    and budget["halted_reason"] in {"budget_exhausted", "actual_cost_exceeded_budget", "actual_cost_exceeded_reservation"}):
                state.update(status="budget_reached", stop_reason="budget_reached")
            _write(cell / "state.json", state)

    def _check_presumption(self, receipts):
        presumption = self.state.get("presumption")
        if not presumption:
            return
        label, request_id = presumption["label"], presumption["request_id"]
        receipt = receipts[label]
        request = next(r for r in receipt["requests"] if r["request_id"] == request_id)
        marker = request["metadata"].get("presumed_zero_recovery", {})
        if presumption.get("revoked") or marker.get("status") == "revoked":
            presumption["revoked"] = True
            self._save()
            self._publish_budget(label, revoked=True)
            return
        if request["state"] == "settled":
            self.state["presumption"]["provider_settled"] = True
            self._save()
            self._publish_budget(label)
            return
        # All actual network attempts must be closed before an aggregate audit.
        if any(r["state"] in {"reserved", "dispatched"} for value in receipts.values() for r in value["requests"]):
            raise RuntimeError("Cannot audit provisional recovery while another request is unresolved")
        matched, evidence = self._stable_audit(receipts)
        if not matched:
            ledger = self._ledger(receipt)
            if ledger.presumed_zero_valid(request_id):
                ledger.revoke_presumed_zero(request_id, evidence_sha256=file_hash(evidence),
                    reason="Exclusive key totals no longer reconcile with known charges")
            presumption.update(revoked=True, revoked_at=self._now())
            self._save()
            self._publish_budget(label, revoked=True)
        elif presumption.get("phase") == "prepared":
            # Complete a crash-interrupted release only after a new idle audit.
            ledger = self._ledger(receipt)
            if not ledger.presumed_zero_valid(request_id):
                ledger.presume_zero(request_id, evidence_sha256=file_hash(evidence),
                    key_sha256=self.state["key_sha256"], baseline_sha256=digest(self.state["baseline"]),
                    expected_receipt_sha256=presumption["expected_receipt_sha256"], exclusive_key=True)
            presumption.update(phase="applied", recovery_audit_sha256=file_hash(evidence))
            self._save()
            self._publish_budget(label)

    @staticmethod
    def _candidate(state, receipt):
        passes = state.get("passes", [])
        latest = max(passes, key=lambda p: p["pass_number"]) if passes else None
        relevant = [r for r in receipt["requests"] if latest is None or r["pass_number"] == latest["pass_number"]]
        if any(r["metadata"].get("protocol_conflict") for r in relevant):
            return False
        if latest is not None and latest.get("validation_healthy") is not True:
            return False
        if state.get("status") in RECOVERABLE:
            return True
        if state.get("status") != "failed" or not passes:
            return False
        return bool(relevant) and relevant[-1]["metadata"].get("transport_failure") is True

    def _reconcile(self, item):
        from .openrouter import OpenRouterRelay, load_openrouter_settings
        from .runner import proof_identity
        cell = self.root / "proofs" / item["label"]
        relay = self.relay_factory(cell, item) if self.relay_factory else OpenRouterRelay(
            cell / "billing", settings=load_openrouter_settings(self.snapshot["config"]["openrouter"]),
            credential_provider=lambda: self._credential()[0], proof_id=proof_identity(self.snapshot, item),
            budget_policy=self.snapshot["config"]["budget_policy"], recovery_policy=self.policy)
        try:
            relay.reconcile_pending()
        finally:
            relay.close()
        self._publish_budget(item["label"])

    def recover(self):
        if self.state is None:
            raise RuntimeError("Initialize recovery before starting workers")
        ready = []
        with self._quiescent():
            receipts = self._collect()
            self._check_presumption(receipts)
            candidates = []
            for item in self.snapshot["proofs"]:
                label = item["label"]
                path = self.root / "proofs" / label / "state.json"
                if label not in receipts or not path.exists() or label in self.state["requeued"]:
                    continue
                if self._candidate(_read(path), receipts[label]):
                    candidates.append(item)
                    self._reconcile(item)
            receipts = self._collect()
            unknown = [(label, r) for label, value in receipts.items() for r in value["requests"] if r["state"] == "unknown"]
            inflight = any(r["state"] in {"reserved", "dispatched"} for value in receipts.values() for r in value["requests"])
            if (self.policy == "exclusive-key-v1" and self.state.get("baseline")
                    and not self.state.get("presumption") and len(unknown) == 1 and not inflight):
                label, request = unknown[0]
                tags = request["metadata"]
                eligible = (label in {p["label"] for p in candidates} and request["generation_id"] is None
                    and not request["usage"] and tags.get("output_observed") is False
                    and type(tags.get("response_headers_received")) is bool and not tags.get("protocol_conflict"))
                finished = tags.get("transport_finished_at")
                if eligible and isinstance(finished, str):
                    ended = datetime.fromisoformat(finished)
                    if ended.tzinfo is None or ended.timestamp() > self.clock():
                        raise RuntimeError("Invalid failed-request finish time")
                    delay = max(0, self.cooldown_seconds - (self.clock() - ended.timestamp()))
                    if delay:
                        self.sleep(delay)
                    matched, evidence = self._stable_audit(receipts)
                    if matched:
                        # Record the once-only choice before releasing any hold.
                        self.state["presumption"] = {"label": label, "request_id": request["request_id"],
                            "evidence_sha256": file_hash(evidence), "at": self._now(), "phase": "prepared",
                            "expected_receipt_sha256": receipt_identity(request)}
                        self._save()
                        self._ledger(receipts[label]).presume_zero(request["request_id"],
                            evidence_sha256=file_hash(evidence), key_sha256=self.state["key_sha256"],
                            baseline_sha256=digest(self.state["baseline"]),
                            expected_receipt_sha256=receipt_identity(request), exclusive_key=True)
                        self.state["presumption"]["phase"] = "applied"
                        self._save()
                        self._publish_budget(label)
                        receipts = self._collect()
            for item in candidates:
                label = item["label"]
                budget = receipts[label]["budget"]
                if (budget["active_requests"] == 0 and budget["halted_reason"] is None
                        and Decimal(budget["remaining_usd"]) > 0):
                    self.state["requeued"][label] = {"at": self._now(), "receipt_sha256": receipts[label]["sha256"]}
                    ready.append(label)
            # A crash after this write can lose a retry, but cannot duplicate it.
            self._save()
            return ready

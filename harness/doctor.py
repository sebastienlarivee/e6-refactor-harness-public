"""Pre-spend checks of explicit snapshots, tooling and unchanged original proofs."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Any

from .benchmark import load_benchmark, file_hash
from .environments import load_environment_map, resolve_benchmark, validate_dependencies


def _values(config: Any) -> dict:
    if isinstance(config, dict):
        return dict(config)
    return config.to_dict()


def _native_environment(elan_home: Path, cache: Path) -> dict[str, str]:
    environment = {key: value for key, value in os.environ.items()
        if not any(word in key.upper() for word in ("API_KEY", "MANAGEMENT_KEY", "SECRET",
            "PASSWORD", "AUTHORIZATION", "ACCESS_TOKEN", "CREDENTIAL", "AUTH_TOKEN", "COOKIE"))
        and not key.upper().startswith(("OPENAI_", "OPENROUTER_"))}
    inherited = [part for part in environment.get("PATH", os.defpath).split(os.pathsep)
        if part.startswith("/") and not part.startswith("/mnt/") and "\\" not in part and ";" not in part]
    environment.update(ELAN_HOME=str(elan_home),
        PATH=os.pathsep.join(dict.fromkeys([str(elan_home / "bin"), *inherited])),
        LEAN_REFACTOR_EVALUATION_CACHE=str(cache / "evaluation"),
        LEAN_REFACTOR_LAUNCH_CACHE=str(cache / "launch"),
        LEAN_NUM_THREADS="1", OMP_NUM_THREADS="1", RAYON_NUM_THREADS="1")
    # Explicit frozen inputs are the only measurement identities in this process.
    for key in ("LEAN_REFACTOR_FINGERPRINT_REGISTRY", "ELAN_TOOLCHAIN", "LEAN_PATH",
                "LEAN_SRC_PATH", "LEAN", "LAKE", "LEAN_SYSROOT", "LAKE_HOME", "LEAN_GITHASH"):
        environment.pop(key, None)
    return environment


def evaluate_original(metadata: dict, directory: Path, *, quick: bool = False,
        timeout_seconds: float = 600, environment: dict[str, str] | None = None) -> dict:
    """Compile original in a subprocess with explicit private caches and no inference."""
    from lean_tools import arena_workflow as arena
    directory.mkdir(parents=True, exist_ok=True)
    _, row = arena.load_task(Path(metadata["task"]))
    task_snapshot = directory / "MeasuredTask.json"
    task_snapshot.write_bytes(Path(metadata["task"]).read_bytes())
    original = directory / "Original.lean"
    original.write_text(arena.render_candidate_scaffold(row), encoding="utf-8", newline="\n")
    environment = environment or _native_environment(Path(metadata["elan_home"]), directory)
    results = []
    for index, project in enumerate([metadata["primary"], *metadata["compatibility"]]):
        output = directory / f"environment-{index:03d}.json"
        request = {"task": str(task_snapshot), "candidate": str(original), "project": project,
            "registry": metadata["registry_source"], "output": str(output),
            "scoring_policy": metadata.get("scoring_policy", "arena-v1"),
            "quick": quick or index > 0, "timeout_seconds": timeout_seconds}
        request_path = directory / f"environment-{index:03d}-request.json"
        request_path.write_text(json.dumps(request), encoding="utf-8")
        result = subprocess.run([sys.executable, "-m", "harness.doctor", "--worker", str(request_path)],
            cwd=Path(__file__).resolve().parents[1], env=environment,
            capture_output=True, text=True, timeout=timeout_seconds + 30)
        if result.returncode or not output.is_file():
            raise ValueError(f"Original check failed at {project}: {(result.stderr or result.stdout)[-4000:]}")
        evaluation = json.loads(output.read_text())
        results.append({"environment": project, "mode": "quick" if request["quick"] else "exact",
            "valid": bool(evaluation.get("valid")), "evaluation": evaluation,
            "evidence_path": str(output), "evidence_sha256": file_hash(output)})
        if not evaluation.get("valid"):
            raise ValueError(f"Original proof did not validate at {project}; see {output}")
        if index == 0 and not quick:
            if evaluation.get("length", {}).get("candidate_tokens") != metadata["original_measurement_tokens"]:
                raise ValueError(f"Original token measurement differs from frozen convention: {row['name']}")
            measured = evaluation.get("heartbeat", {}).get("candidate")
            if type(measured) is not int or measured <= 0:
                raise ValueError(f"Original lacks exact heartbeat evidence: {row['name']}")
    evidence = {"task_id": row["name"], "label": metadata["label"], "status": "passed",
        "task_path": str(task_snapshot), "task_sha256": file_hash(task_snapshot),
        "original_path": str(original), "original_sha256": file_hash(original), "environments": results}
    from .baselines import validate_original_evidence
    validate_original_evidence(metadata, evidence, quick=quick)
    return evidence


def check(config: Any, env_map=None, *, quick: bool = False,
        output_dir: str | Path | None = None, metadata: list[dict] | None = None,
        receipt_dir: str | Path | None = None) -> dict:
    """Return a durable honest report; quick still compiles every selected original."""
    values = _values(config)
    temporary = tempfile.TemporaryDirectory(prefix="lean-harness-doctor-") if output_dir is None else None
    output = Path(output_dir or temporary.name).resolve()
    output.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    report = {"schema_version": 1, "status": "checking", "mode": "quick" if quick else "full",
        "checks": [], "proofs": [], "failures": [], "output_dir": str(output),
        "paid_inference": False}
    def record(name, function):
        try:
            detail = function()
            report["checks"].append({"name": name, "status": "passed", "detail": detail})
            return detail
        except Exception as error:
            detail = {"name": name, "status": "failed", "error_type": type(error).__name__, "error": str(error)}
            report["checks"].append(detail)
            report["failures"].append(detail)
            return None
    def tooling():
        if sys.platform != "linux" or sys.version_info < (3, 12):
            raise ValueError("Native Linux with Python >=3.12 is required")
        codex, elan = Path(values["codex"]), Path(values["elan_home"])
        if not codex.is_absolute() or str(codex).startswith("/mnt/") or codex.suffix == ".exe" or not os.access(codex, os.X_OK):
            raise ValueError("Explicit native Linux Codex executable is required")
        environment = _native_environment(elan, output / "cache")
        version = subprocess.run([str(codex), "--version"], env=environment, capture_output=True, text=True, timeout=15, check=True).stdout.strip()
        if version != "codex-cli 0.164.0":
            raise ValueError(f"Pinned Codex CLI 0.164.0 required, got {version!r}")
        for tool in ("lean", "lake", "elan"):
            if not os.access(elan / "bin" / tool, os.X_OK):
                raise ValueError(f"Missing explicit native launcher: {elan / 'bin' / tool}")
        for tool in ("git", "bwrap"):
            if not shutil.which(tool, path=environment["PATH"]):
                raise ValueError(f"Missing required tooling: {tool}")
        subprocess.run(["bwrap", "--die-with-parent", "--unshare-user", "--ro-bind", "/", "/", "/bin/true"],
            env=environment, capture_output=True, text=True, timeout=15, check=True)
        return {"python": sys.version.split()[0], "codex": str(codex), "codex_version": version,
            "bubblewrap": "user namespace and read-only root verified"}
    tool_result = record("native-tooling", tooling)
    benchmark = record("contest-input", lambda: load_benchmark(values["input_path"], values.get("heartbeat_path")))
    if benchmark is not None:
        # Do not serialize original proof text into the tooling summary.
        report["checks"][-1]["detail"] = benchmark.to_dict()
    binding = record("environment-map", lambda: load_environment_map(env_map or values["env_map"]))
    if binding is not None:
        report["checks"][-1]["detail"] = {"path": str(binding.path), "identity": binding.identity}
    supplied_metadata = metadata
    metadata = None
    if benchmark is not None and binding is not None:
        metadata = record("pinned-snapshots", lambda: supplied_metadata if supplied_metadata is not None else resolve_benchmark(benchmark, binding,
            output / "benchmark", selected=values.get("selected_proofs", ()),
            elan_home=Path(values["elan_home"])))
        if metadata is not None:
            report["checks"][-1]["detail"] = {"proof_count": len(metadata),
                "snapshot_count": len({e["snapshot_id"] for m in metadata for e in m["environments"]})}
    report["resolved_proofs"] = []
    if metadata is not None and tool_result is not None:
        for item in metadata:
            try:
                from lean_tools import arena_workflow as arena
                _, row = arena.load_task(Path(item["task"]))
                dependencies = [validate_dependencies(row, Path(project), elan_home=Path(values["elan_home"]))
                    for project in [item["primary"], *item["compatibility"]]]
                evidence = evaluate_original(item, output / "proofs" / item["label"], quick=quick)
                evidence["dependencies"] = dependencies
                if not quick:
                    from .baselines import freeze_original_baseline
                    resolved = freeze_original_baseline(item, evidence, Path(receipt_dir or output / "baselines"))
                    evidence["baseline_receipt"] = resolved["baseline_receipt"]
                    evidence["baseline_provenance"] = resolved["baseline_provenance"]
                    report["resolved_proofs"].append(resolved)
                else:
                    report["resolved_proofs"].append(item)
                report["proofs"].append(evidence)
            except Exception as error:
                failure = {"label": item["label"], "task_id": item["task_id"], "status": "failed",
                    "error_type": type(error).__name__, "error": str(error)}
                report["proofs"].append(failure)
                report["failures"].append(failure)
    report.update(status="failed" if report["failures"] else "passed",
        elapsed_seconds=round(time.monotonic() - started, 3))
    report["evidence_persisted"] = temporary is None
    (output / "doctor.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    if temporary:
        # Keep meaningful report contents, while clearly identifying ephemeral evidence.
        report["evidence_persisted"] = False
        temporary.cleanup()
    else:
        report["evidence_persisted"] = True
    return report


def _worker(path: Path):
    from lean_tools import arena_workflow as arena
    from lean_tools.measurement_policy import scoring_policy_context
    request = json.loads(path.read_text())
    with scoring_policy_context(request["scoring_policy"]):
        value = arena.evaluate_candidate(Path(request["task"]), Path(request["candidate"]),
            Path(request["project"]), quick=request["quick"],
            timeout_seconds=request["timeout_seconds"], fingerprint_registry=Path(request["registry"]))
    Path(request["output"]).write_text(json.dumps(arena.evaluation_payload(value), ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] != "--worker":
        raise SystemExit("Use the public harness doctor command")
    _worker(Path(sys.argv[2]))

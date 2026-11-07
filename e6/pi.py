"""Pinned, fresh Pi SDK proof agents routed exclusively through the E6 meter."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from .config import runtime_root

MODEL = "gpt-6.1-sol"
TOKEN_ENV = "LRH_SERIAL_MODEL_TOKEN"
WORKER = Path(__file__).with_name("pi_worker.mjs").resolve()
DEFAULT_RELEASE = Path.home() / ".pi/agent/install/releases/1.1.0"
DEFAULT_NODE = Path.home() / ".local/node-v22.22.3/bin/node"


def validate_settings(config: dict) -> None:
    """Reject unsupported Pi treatments before runtime or inference setup."""
    from .experiment import experiment_spec
    spec = experiment_spec(config)
    if spec.model != MODEL or spec.reasoning_effort != "xhigh" or spec.service_tier != "default":
        raise ValueError("Pi requires the pinned gpt-6.1-sol xhigh default-tier treatment")


def _sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _tree_sha(root: Path) -> str:
    """Fingerprint all executable SDK code/dependencies, including link targets."""
    digest = hashlib.sha256()
    for path in sorted(root.rglob("*")):
        if path.is_file():
            digest.update(path.relative_to(root).as_posix().encode() + b"\0")
            digest.update(_sha(path).encode() + b"\n")
        elif path.is_symlink():
            digest.update(path.relative_to(root).as_posix().encode() + b"\0")
            digest.update(os.readlink(path).encode() + b"\n")
    return digest.hexdigest()


def ripgrep() -> Path:
    """Reuse one native binary; never download into a fresh proof capsule."""
    configured = os.environ.get("E6_PI_RG")
    cached_codex = (runtime_root() / "bin/codex").resolve()
    candidates = [configured] if configured is not None else [
        shutil.which("rg"), runtime_root() / "bin/rg", Path.home() / ".pi/agent/bin/rg",
        cached_codex.parent.parent / "codex-path/rg",
    ]
    for value in candidates:
        if value is None:
            continue
        path = Path(value).expanduser()
        if not path.is_absolute():
            continue
        path = path.resolve()
        if path.is_file() and os.access(path, os.X_OK) and path.suffix != ".exe":
            return path
    raise RuntimeError("Pi requires existing native ripgrep (rg); set E6_PI_RG to its executable")


def runtime() -> dict:
    """Resolve and fingerprint the installed runtime without model/auth requests."""
    release = Path(os.environ.get("E6_PI_RELEASE", str(DEFAULT_RELEASE))).expanduser().resolve()
    package = release / "node_modules/@earendil-works/pi-coding-agent"
    node = Path(os.environ.get("E6_PI_NODE", str(DEFAULT_NODE))).expanduser().resolve()
    if not node.is_file() or not os.access(node, os.X_OK):
        raise RuntimeError(f"Pi requires an executable Node runtime: {node}")
    if not (package / "dist/index.js").is_file() or not (release / "package-lock.json").is_file():
        raise RuntimeError(f"Pi SDK release is incomplete: {release}")
    manifest = json.loads((package / "package.json").read_text(encoding="utf-8"))
    if manifest.get("name") != "@earendil-works/pi-coding-agent":
        raise RuntimeError("Unexpected Pi SDK package")
    rg = ripgrep()
    result = subprocess.run([str(node), "--version"], capture_output=True, text=True, check=True)
    return {"pi_node": str(node), "pi_package": str(package), "pi_release": str(release),
            "pi_rg": str(rg),
            "pi_version": manifest["version"], "pi_identity": {
                "node_sha256": _sha(node), "node_version": result.stdout.strip(),
                "rg_sha256": _sha(rg),
                "package_lock_sha256": _sha(release / "package-lock.json"),
                "release_sha256": _tree_sha(release)}}


def verify_runtime(config: dict) -> None:
    """Fail closed if the frozen native Node/SDK/dependencies have drifted."""
    validate_settings(config)
    if not config.get("pi_rg") or not config.get("pi_identity", {}).get("rg_sha256"):
        raise RuntimeError("Prepared Pi runtime lacks pinned ripgrep; prepare a new run")
    node, release = Path(config["pi_node"]), Path(config["pi_release"])
    rg = Path(config["pi_rg"])
    if not rg.is_absolute() or not rg.is_file() or not os.access(rg, os.X_OK) or rg.suffix == ".exe":
        raise RuntimeError("Prepared Pi ripgrep is not a native executable")
    package = Path(config["pi_package"])
    if package.resolve() != (release / "node_modules/@earendil-works/pi-coding-agent").resolve():
        raise RuntimeError("Prepared Pi package is outside the pinned release")
    manifest = json.loads((package / "package.json").read_text(encoding="utf-8"))
    identity = config.get("pi_identity", {})
    observed = {"node_sha256": _sha(node),
                "rg_sha256": _sha(rg),
                "node_version": subprocess.run([str(node), "--version"], check=True,
                    capture_output=True, text=True).stdout.strip(),
                "package_lock_sha256": _sha(release / "package-lock.json"),
                "release_sha256": _tree_sha(release)}
    if manifest.get("version") != config["pi_version"] or observed != identity:
        raise RuntimeError("Prepared Pi runtime changed")


def command(config: dict, capsule: Path, url: str | None = None) -> list[str]:
    """One prompt on stdin; JSONL events on stdout and pi-final.txt in the capsule."""
    validate_settings(config)
    argv = [str(config["pi_node"]), str(WORKER), "--package", str(config["pi_package"]),
            "--capsule", str(capsule.resolve()), "--catalog", str(config["model_catalog"]),
            "--python", str(config.get("pi_python", Path(sys.executable).resolve())),
            "--feedback-script", str(Path(__file__).resolve().parents[1] / "lean_tools/feedback_workflow.py")]
    if url is not None:
        argv += ["--relay", url]
    # exec replaces Linux's original /proc/PID/environ, which deleting process.env
    # alone cannot do. fd 3 is an anonymous pipe consumed/closed before tool startup.
    bootstrap = 'exec 3<<<"$LRH_SERIAL_MODEL_TOKEN"; unset LRH_SERIAL_MODEL_TOKEN; exec "$@"'
    return ["/bin/bash", "-c", bootstrap, "e6-pi", *argv]


def preflight(config: dict, capsule: Path, output: Path | None = None) -> dict:
    """Validate SDK, pinned model and native MCP metadata without inference."""
    verify_runtime(config)
    environment = {key: value for key, value in os.environ.items()
                   if key != TOKEN_ENV and not any(part in key.upper()
                   for part in ("API_KEY", "ACCESS_TOKEN", "REFRESH_TOKEN", "PASSWORD", "SECRET"))}
    environment.update(PI_OFFLINE="1", PI_CODING_AGENT_DIR=str(capsule / ".native-home/.pi/agent"),
                       HOME=str(capsule / ".native-home"))
    from .isolation import wrap_command
    # Metadata runs use exactly the same filesystem boundary as proof agents.
    argv, environment = wrap_command({**config, "agent_backend": "pi"}, capsule,
        command(config, capsule) + ["--preflight"], [capsule], environment)
    # The native MCP endpoint is local and no model token is supplied.
    result = subprocess.run(argv, cwd=capsule,
                            env=environment, capture_output=True, text=True, timeout=60)
    try:
        rows = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
        report = next(row for row in reversed(rows) if row.get("type") == "preflight")
    except (ValueError, StopIteration) as error:
        raise RuntimeError(f"Pi metadata preflight did not return JSON (exit {result.returncode})") from error
    if output is not None:
        Path(output).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if result.returncode or report.get("status") != "passed":
        raise RuntimeError(f"Pi metadata preflight failed: {report.get('error', 'unknown failure')}")
    return report

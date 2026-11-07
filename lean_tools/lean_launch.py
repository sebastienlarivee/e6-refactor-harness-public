"""Opt-in, guarded reuse of Lake's environment for cold Lean processes.

LEAN_REFACTOR_LAUNCH_CACHE names a cache directory. Preparation only reads an
already materialized workspace: missing dependencies or compiled lakefiles are
errors, never invitations to build or download. Only the explicit environment
whitelist is exported/persisted; other child variables come from the caller.
"""
from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import hashlib
import json
import math
import os
import re
import signal
import subprocess
import sys
import time
import uuid
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from lean_tools import resource_gate, process_memory
CACHE_ENV = "LEAN_REFACTOR_LAUNCH_CACHE"
SCHEMA_VERSION = 1
# Lake v4.26 Workspace.augmentedEnvVars / Env.baseVars, restricted to paths and
# compiler identity. In particular, LAKE_CACHE_KEY and service credentials never
# leave the current ambient environment or enter a cache/log.
ENVIRONMENT_KEYS = (
    "PATH", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN", "LEAN_GITHASH",
    "LAKE", "LAKE_HOME", "ELAN", "ELAN_HOME", "ELAN_TOOLCHAIN", "LEAN_AR",
    "LEAN_CC", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH",
)
AMBIENT_PATH_KEYS = (
    "PATH", "PATHEXT", "HOME", "USERPROFILE", "LOCALAPPDATA", "APPDATA",
    "XDG_CACHE_HOME", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH",
)


def native_command(command: list[str]) -> list[str]:
    """Give future Linux Lean processes the checkpoint's background priority."""
    if sys.platform != "linux":
        return command
    increment = max(0, 10 - os.getpriority(os.PRIO_PROCESS, 0))
    return ["/usr/bin/nice", "-n", str(increment), *command] if increment else command


def native_environment(environment: Mapping[str, str] | None = None) -> dict[str, str]:
    """Use one compiler thread and one native worker in the Linux lane."""
    result = dict(os.environ if environment is None else environment)
    if sys.platform == "linux":
        result.update(LEAN_NUM_THREADS="1", OMP_NUM_THREADS="1", RAYON_NUM_THREADS="1")
    return result


class LaunchCacheError(RuntimeError):
    pass


@dataclass(frozen=True)
class LaunchEnvironment:
    executable: str
    environment: dict[str, str]
    provenance: dict[str, Any]


def _digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode("utf-8")).hexdigest()


def _same_path(value: Any, expected: str | Path) -> bool:
    if not isinstance(value, str) or not value:
        return False
    return os.path.normcase(str(Path(value).resolve())) == os.path.normcase(str(Path(expected).resolve()))


def _valid_export(value: Any, guard: dict[str, Any]) -> bool:
    return (
        isinstance(value, dict) and set(value) == set(ENVIRONMENT_KEYS)
        and all(item is None or isinstance(item, str) for item in value.values())
        and _same_path(value.get("LEAN"), guard["executable"])
        and _same_path(value.get("LEAN_SYSROOT"), Path(guard["executable"]).parent.parent)
        and value.get("LEAN_GITHASH") == guard["githash"]
    )


def _remaining(deadline: float | None) -> float | None:
    if deadline is None:
        return None
    remaining = deadline - time.perf_counter()
    if remaining <= 0:
        raise LaunchCacheError("Lean launch preparation deadline expired")
    return remaining


def _file(path: Path, *, content: bool = True) -> dict[str, Any]:
    try:
        stat = path.stat()
        if not path.is_file():
            raise OSError("not a file")
        identity = {
            "path": str(path.resolve()), "size": stat.st_size,
            "mtime_ns": stat.st_mtime_ns, "inode": stat.st_ino,
        }
        if content:
            identity["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        return identity
    except OSError as error:
        raise LaunchCacheError(f"launch cache requires materialized file: {path}") from error


def _git_head(package: Path, *, allow_unborn: bool = False) -> str | None:
    git_dir = package / ".git"
    if git_dir.is_file():
        line = git_dir.read_text(encoding="utf-8").strip()
        if not line.startswith("gitdir: "):
            raise LaunchCacheError(f"invalid package Git directory: {package}")
        git_dir = (package / line[8:]).resolve()
    common = git_dir
    if (git_dir / "commondir").is_file():
        common = (git_dir / (git_dir / "commondir").read_text().strip()).resolve()
    try:
        head = (git_dir / "HEAD").read_text(encoding="utf-8").strip()
        if head.startswith("ref: "):
            ref = head[5:]
            if not ref.startswith("refs/") or ".." in Path(ref).parts:
                raise LaunchCacheError(f"invalid package Git ref: {package}")
            ref_file = common / ref
            if ref_file.is_file():
                head = ref_file.read_text(encoding="utf-8").strip()
            else:
                packed = common / "packed-refs"
                entries = packed.read_text(encoding="utf-8").splitlines() if packed.is_file() else []
                matches = [line.split()[0] for line in entries if line.endswith(" " + ref)]
                if not matches and allow_unborn:
                    return None
                if len(matches) != 1:
                    raise LaunchCacheError(f"cannot resolve package Git HEAD: {package}")
                head = matches[0]
        if not re.fullmatch(r"[0-9a-f]{40}", head):
            raise LaunchCacheError(f"invalid package Git HEAD: {package}")
        return head
    except OSError as error:
        raise LaunchCacheError(f"launch cache requires package Git HEAD: {package}") from error


def lake_text_hash(text: str) -> str:
    """Lake Hash.ofText (Murmur64A seed 11, then mixHash 1723).

    See Lean v4.26 runtime/hash.cpp, runtime/hash.h and Lake/Build/Trace.lean.
    This checks existing configuration traces without running Lean.
    """
    data = text.replace("\r\n", "\n").encode("utf-8")
    mask, multiplier = (1 << 64) - 1, 0xC6A4A7935BD1E995
    value = (11 ^ (len(data) * multiplier)) & mask
    end = len(data) // 8 * 8
    for offset in range(0, end, 8):
        block = int.from_bytes(data[offset:offset + 8], sys.byteorder)
        block = block * multiplier & mask
        block ^= block >> 47
        block = block * multiplier & mask
        value = ((value ^ block) * multiplier) & mask
    if end < len(data):
        value ^= int.from_bytes(data[end:], "little")
        value = value * multiplier & mask
    value ^= value >> 47
    value = value * multiplier & mask
    value ^= value >> 47
    value = value * multiplier & mask
    value ^= value >> 47
    value ^= multiplier
    return f"{((1723 ^ value) * multiplier) & mask:016x}"


def _compiled_config(
    package: Path, root: Path, name: str, config: Path, githash: str, platform: str,
    *, index: int, indexed_configs: bool,
) -> list[dict[str, Any]]:
    if config.suffix != ".lean":
        return []
    # Only accept the location the pinned Lake loader actually uses. Finding an
    # older artifact elsewhere must not cause Lake to recompile a configuration.
    config_dir = root / ".lake/config" / str(index) if indexed_configs else (
        package / ".lake/config" / name.strip("«»")
    )
    candidates = [config_dir / (config.stem + ".olean.trace")]
    expected_hash = lake_text_hash(config.read_text(encoding="utf-8"))
    for trace in sorted(candidates):
        try:
            value = json.loads(trace.read_text(encoding="utf-8"))
            olean = trace.with_suffix("")
            if (
                value.get("name") == name and value.get("configHash") == expected_hash
                and value.get("leanHash") == githash and value.get("platform") == platform
                and isinstance(value.get("options"), dict) and olean.is_file()
                and (value.get("idx") == index if indexed_configs else
                     ("idx" not in value or value["idx"] == index))
            ):
                return [_file(trace), _file(olean, content=False)]
        except (OSError, ValueError, AttributeError):
            continue
    raise LaunchCacheError(f"launch cache requires an up-to-date compiled lakefile: {config}")


def add_lean_path_prefixes(
    child: dict[str, str], ambient: Mapping[str, str], prefixes: list[Path],
) -> None:
    """Match `lake env` ordering: workspace, supplied prefixes, ambient path."""
    if not prefixes:
        return
    resolved = child.get("LEAN_PATH", "").split(os.pathsep)
    resolved = [part for part in resolved if part]
    inherited = [part for part in ambient.get("LEAN_PATH", "").split(os.pathsep) if part]
    if inherited and resolved[-len(inherited):] != inherited:
        raise LaunchCacheError("cached Lean path does not preserve the guarded ambient suffix")
    workspace = resolved[:-len(inherited)] if inherited else resolved
    child["LEAN_PATH"] = os.pathsep.join([
        *workspace, *(str(path.resolve()) for path in prefixes), *inherited,
    ])


def workspace_guard(project_root: Path, environment: Mapping[str, str]) -> dict[str, Any]:
    root = project_root.resolve()
    toolchain_file = root / "lean-toolchain"
    _file(toolchain_file)
    toolchain = toolchain_file.read_text(encoding="utf-8").strip()
    if not re.fullmatch(r"leanprover/lean4:v4\.\d+\.\d+(?:-rc\d+)?", toolchain):
        raise LaunchCacheError("launch cache requires a pinned Lean release toolchain")
    elan_home = Path(environment.get("ELAN_HOME") or str(Path.home() / ".elan")).expanduser().resolve()
    install = elan_home / "toolchains" / toolchain.replace("/", "--").replace(":", "---")
    executable_suffix = ".exe" if os.name == "nt" else ""
    lean = (install / "bin" / ("lean" + executable_suffix)).resolve()
    lake = (install / "bin" / ("lake" + executable_suffix)).resolve()
    files = [_file(toolchain_file), _file(lean, content=False), _file(lake, content=False)]
    for key, expected in (("LEAN", lean), ("LAKE", lake), ("LEAN_SYSROOT", install), ("LAKE_HOME", install)):
        if environment.get(key) and Path(environment[key]).resolve() != expected.resolve():
            raise LaunchCacheError(f"{key} conflicts with the pinned project toolchain")
    if environment.get("ELAN_TOOLCHAIN") not in (None, "", toolchain):
        raise LaunchCacheError("ELAN_TOOLCHAIN conflicts with the pinned project toolchain")
    if environment.get("LAKE_OVERRIDE_LEAN"):
        raise LaunchCacheError("launch cache does not support LAKE_OVERRIDE_LEAN")
    header = install / "lib/lean/Init.olean"
    files.append(_file(header, content=False))
    with header.open("rb") as stream:
        prefix = stream.read(96)
    hashes = re.findall(rb"[0-9a-f]{40}", prefix)
    if not prefix.startswith(b"olean") or len(hashes) != 1:
        raise LaunchCacheError("cannot read pinned toolchain identity from Init.olean")
    githash = hashes[0].decode("ascii")
    version_header = install / "include/lean/version.h"
    files.append(_file(version_header))
    matches = re.findall(r'^#define LEAN_PLATFORM_TARGET "([^"]+)"', version_header.read_text(), re.MULTILINE)
    if len(matches) != 1:
        raise LaunchCacheError("cannot read pinned toolchain platform")
    platform = matches[0]
    # Lake 4.30 moved compiled configurations into the workspace, indexed in
    # materialization order (the order preserved in a generated manifest).
    minor_version = int(toolchain.split(":v4.")[1].split(".")[0])
    indexed_configs = minor_version >= 30
    if environment.get("LEAN_GITHASH") not in (None, "", githash):
        raise LaunchCacheError("LEAN_GITHASH conflicts with the pinned project toolchain")
    manifest_path = root / "lake-manifest.json"
    files.append(_file(manifest_path))
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        packages = manifest["packages"]
        if not isinstance(packages, list):
            raise ValueError("packages is not a list")
        packages_dir = root / manifest.get("packagesDir", ".lake/packages")
        package_specs = [(root, str(manifest["name"]), None, 0)]
        heads: list[dict[str, str | None]] = []
        for index, package in enumerate(packages, start=1):
            name = package["name"]
            directory_name = name.strip("«»")
            if not re.fullmatch(r"[A-Za-z0-9_.-]+", directory_name):
                raise LaunchCacheError("launch cache requires simple materialized package names")
            if package.get("type") == "git":
                directory = packages_dir / directory_name
                actual_head = _git_head(directory)
                if actual_head != package["rev"]:
                    raise LaunchCacheError(f"package HEAD differs from its manifest pin: {name}")
                heads.append({"root": str(directory.resolve()), "head": actual_head})
                package_root = directory / (package.get("subDir") or "")
            elif package.get("type") == "path":
                package_root = root / package["dir"]
                if (package_root / ".git").exists():
                    # Existing exported path packages may have an unborn Git
                    # stub. Lake never materializes/fetches a path dependency.
                    heads.append({"root": str(package_root.resolve()),
                                  "head": _git_head(package_root, allow_unborn=True)})
            else:
                raise LaunchCacheError("launch cache requires materialized Git or path packages")
            package_specs.append((package_root, name, package.get("configFile"), index))
        for directory, name, config_name, index in package_specs:
            if (directory / ".lake/package-overrides.json").exists():
                raise LaunchCacheError("launch cache does not support Lake package overrides")
            configs = [directory / config_name] if config_name else [
                directory / "lakefile.lean", directory / "lakefile.toml",
            ]
            configs = [config for config in configs if config.is_file()]
            if not configs:
                raise LaunchCacheError(f"launch cache requires package configuration: {directory}")
            for config in configs:
                files.append(_file(config))
                files.extend(_compiled_config(directory, root, name, config, githash, platform,
                                              index=index, indexed_configs=indexed_configs))
            for filename in ("lean-toolchain", "lake-manifest.json"):
                optional = directory / filename
                if optional.is_file():
                    files.append(_file(optional))
    except (KeyError, TypeError, ValueError) as error:
        raise LaunchCacheError("invalid launch cache workspace manifest") from error
    relevant = {
        key: _digest(value) for key, value in environment.items()
        if key in AMBIENT_PATH_KEYS or key.startswith(("LAKE_", "ELAN_"))
        or (key.startswith("LEAN_") and not key.startswith("LEAN_REFACTOR_"))
    }
    return {
        "project_root": str(root), "toolchain": toolchain, "executable": str(lean),
        "lake": str(lake), "githash": githash, "platform": platform,
        "files": files, "package_heads": heads, "ambient_hashes": relevant,
    }


def _terminate(process: subprocess.Popen[str]) -> None:
    # Linux cleanup targets a live owned child, with its captured creation tick.
    # Windows retains the bounded tree-kill and leader fallback.
    if os.name == "nt":
        try:
            subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                           capture_output=True, check=False, timeout=10)
        except (OSError, subprocess.TimeoutExpired):
            pass
    elif sys.platform == "linux":
        # A completed Popen has already surrendered its PID; never target a
        # later process that happened to receive that number.
        if process.poll() is None:
            process_memory.terminate_process_tree_pid(
                process.pid, expected_start_time=getattr(process, "_lean_start_time", None),
            )
        return
    else:
        try:
            if os.getpgid(process.pid) != os.getpgrp():
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
    # taskkill may fail or time out; kill the owned leader as a bounded fallback.
    if process.poll() is None:
        try:
            process.kill()
        except OSError:
            pass


def drain_process(process: subprocess.Popen[str], error: subprocess.TimeoutExpired) -> tuple[str, str | None]:
    """Drain an already-terminated tree without trusting inherited pipe closure."""
    try:
        return process.communicate(timeout=5)
    except subprocess.TimeoutExpired as drain_error:
        _terminate(process)
        for stream in (process.stdout, process.stderr):
            if stream is not None:
                stream.close()
        def decoded(value: str | bytes | None) -> str:
            return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else value or ""
        return decoded(drain_error.output or error.output), decoded(drain_error.stderr or error.stderr)


def prepare_launch(
    project_root: Path, *, deadline: float | None, environment: Mapping[str, str] | None = None,
    export_timeout_seconds: float | None = None,
    terminate_process: Callable[[subprocess.Popen[str]], None] | None = None,
    record_event: Callable[[str, dict[str, Any]], Any] | None = None,
) -> LaunchEnvironment:
    """Export once per guard; optionally separate lock wait from exporter work.

    Historical callers supply an absolute deadline. A caller with no queue budget
    supplies deadline=None and a finite exporter watchdog instead.
    """
    if deadline is None and (isinstance(export_timeout_seconds, bool)
        or not isinstance(export_timeout_seconds, (int, float))
        or not math.isfinite(export_timeout_seconds) or export_timeout_seconds <= 0):
        raise LaunchCacheError("a finite positive exporter watchdog is required without a launch deadline")
    ambient = dict(os.environ if environment is None else environment)
    cache_value = ambient.get(CACHE_ENV)
    if not cache_value:
        raise LaunchCacheError(f"{CACHE_ENV} must name a cache directory")
    cache_root = Path(cache_value).expanduser().resolve()
    root_key = _digest(str(project_root.resolve()))
    project_cache = cache_root / root_key
    started = time.perf_counter()
    provenance: dict[str, Any] = {"project_root": str(project_root.resolve())}
    try:
        _remaining(deadline)
        pool = resource_gate.FilePermitPool(cache_root / ".locks", root_key, 1)
        with pool.acquire(timeout_seconds=_remaining(deadline)):
            guard = workspace_guard(project_root, ambient)
            _remaining(deadline)
            guard_hash = _digest(guard)
            # Keep separately guarded host/sandbox PATH variants, rather than
            # repeatedly overwriting one project's capture between contexts.
            cache_path = project_cache / f"{guard_hash}.json"
            provenance.update(cache_path=str(cache_path), guard_hash=guard_hash,
                              toolchain=guard["toolchain"], executable=guard["executable"])
            previous = resource_gate.read_json(cache_path)
            exported = previous.get("environment") if previous else None
            if (
                previous and previous.get("schema_version") == SCHEMA_VERSION
                and previous.get("guard") == guard and _valid_export(exported, guard)
                and previous.get("environment_hash") == _digest(exported)
            ):
                provenance["status"] = "hit"
            else:
                provenance["status"] = "stale" if any(project_cache.glob("*.json")) else "miss"
                exporter = (
                    "import json, os; print(json.dumps({k: os.environ.get(k) for k in "
                    + repr(ENVIRONMENT_KEYS) + "}, sort_keys=True))"
                )
                command = [guard["lake"], "env", str(Path(sys.executable).resolve()), "-c", exporter]
                _remaining(deadline)
                process = subprocess.Popen(
                    command, cwd=project_root, env=ambient, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="replace",
                    creationflags=subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0,
                    start_new_session=os.name != "nt",
                )
                process_memory.capture_process_identity(process)
                try:
                    stdout, stderr = process.communicate(timeout=(
                        _remaining(deadline) if deadline is not None else export_timeout_seconds
                    ))
                except (subprocess.TimeoutExpired, LaunchCacheError) as error:
                    # A bounded drain prevents grandchildren holding pipes open
                    # from turning a preparation timeout into an unbounded wait.
                    (terminate_process or _terminate)(process)
                    drain_process(process, error if isinstance(error, subprocess.TimeoutExpired)
                                  else subprocess.TimeoutExpired(command, 0))
                    raise LaunchCacheError("Lake environment exporter timed out") from error
                provenance.update(export_returncode=process.returncode,
                                  stdout_bytes=len(stdout.encode("utf-8")),
                                  stderr_bytes=len(stderr.encode("utf-8")),
                                  stderr_sha256=hashlib.sha256(stderr.encode("utf-8")).hexdigest())
                if process.returncode != 0:
                    raise LaunchCacheError(f"Lake environment exporter failed ({process.returncode}); output withheld")
                try:
                    exported = json.loads(stdout)
                except ValueError as error:
                    raise LaunchCacheError("Lake environment exporter returned invalid JSON; output withheld") from error
                if not _valid_export(exported, guard):
                    raise LaunchCacheError("Lake environment exporter did not resolve the pinned toolchain whitelist")
                # Lake can spell the Windows drive letter differently from
                # pathlib. Persist the exact guarded absolute compiler path.
                exported["LEAN"] = guard["executable"]
                exported["LEAN_SYSROOT"] = str(Path(guard["executable"]).parent.parent)
                _remaining(deadline)
                if workspace_guard(project_root, ambient) != guard:
                    raise LaunchCacheError("workspace changed during Lake environment export; cache not written")
                payload = {"schema_version": SCHEMA_VERSION, "guard": guard,
                           "environment": exported, "environment_hash": _digest(exported),
                           "capture": provenance.copy()}
                project_cache.mkdir(parents=True, exist_ok=True)
                temporary = cache_path.with_name(f".{cache_path.name}.{uuid.uuid4().hex}.tmp")
                try:
                    temporary.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8")
                    temporary.replace(cache_path)
                finally:
                    temporary.unlink(missing_ok=True)
            child = ambient.copy()
            for key, value in exported.items():
                if value is None:
                    child.pop(key, None)
                else:
                    child[key] = value
            _remaining(deadline)
        provenance["seconds"] = round(time.perf_counter() - started, 6)
        if record_event:
            record_event("lean_launch_cache", provenance.copy())
        return LaunchEnvironment(guard["executable"], child, provenance)
    except (LaunchCacheError, resource_gate.ResourceGateError, OSError) as error:
        provenance.update(status="failed", seconds=round(time.perf_counter() - started, 6), error=str(error))
        if record_event:
            record_event("lean_launch_cache", provenance.copy())
        if isinstance(error, LaunchCacheError):
            raise
        raise LaunchCacheError(f"Lean launch cache preparation failed: {error}") from error

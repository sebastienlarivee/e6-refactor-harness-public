"""Materialize public pinned Git sources for organizer environment setup."""
from __future__ import annotations

import fcntl
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
from urllib.parse import urlsplit


def coordinate(value: object) -> dict[str, str]:
    """Accept one public GitHub repository and an immutable full commit hash."""
    if not isinstance(value, dict) or set(value) != {"url", "rev"}:
        raise ValueError("Upstream source requires url and rev")
    url, revision = value["url"], value["rev"]
    if not isinstance(url, str) or not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Upstream source requires a full 40-character commit revision")
    parsed = urlsplit(url)
    parts = parsed.path.rstrip("/").removesuffix(".git").split("/")
    if (parsed.scheme != "https" or parsed.netloc != "github.com" or parsed.query or parsed.fragment
            or len(parts) != 3 or parts[0] or any(
                not re.fullmatch(r"[A-Za-z0-9_.-]+", part) or part in {".", ".."} for part in parts[1:])):
        raise ValueError("Upstream source requires a public HTTPS GitHub repository without credentials")
    return {"url": "https://github.com/" + "/".join(parts[1:]), "rev": revision}


def _relative(value: object) -> PurePosixPath:
    if (not isinstance(value, str) or not value or "\\" in value or ":" in value
            or any(part in {"", ".", "..", ".git"} for part in value.split("/"))):
        raise ValueError(f"Unsafe upstream source path: {value}")
    path = PurePosixPath(value)
    if path.is_absolute():
        raise ValueError(f"Unsafe upstream source path: {value}")
    return path


def source_plan(spec: dict, item: dict) -> tuple[dict | None, list[tuple[PurePosixPath, dict]]]:
    """Validate portable source coordinates and package placement without fetching."""
    overlays = item["overlays"]
    try:
        stage = json.loads(overlays[".lrh-stage.json"])
        manifest = json.loads(overlays["lake-manifest.json"])
    except (KeyError, TypeError, json.JSONDecodeError) as error:
        raise ValueError("Upstream setup requires stage and Lake manifest overlays") from error
    if (not isinstance(stage, dict) or stage.get("schema_version") != 1
            or stage.get("lean_version") != spec["lean_version"] or stage.get("revision") != spec["revision"]):
        raise ValueError("Upstream stage identity differs from its pinned requirement")
    expected = coordinate({"url": spec["repository"], "rev": spec["revision"]})
    if "source" not in item:
        raise ValueError("Upstream snapshot requires an explicit source or null generated root")
    source = None if item["source"] is None else coordinate(item["source"])
    if source is None:
        if stage.get("kind") != "putnam" or expected["url"] != "https://github.com/leanprover-community/mathlib4":
            raise ValueError("Only generated Putnam roots may omit an upstream source")
    elif source != expected or stage.get("kind") != "repository":
        raise ValueError("Upstream root source differs from its pinned requirement")
    if not isinstance(manifest, dict) or not isinstance(manifest.get("packages"), list):
        raise ValueError("Upstream setup requires a complete Lake package manifest")
    packages_dir = _relative(manifest.get("packagesDir", ".lake/packages"))
    packages = []
    for entry in manifest["packages"]:
        if not isinstance(entry, dict) or entry.get("type") not in {"git", "path"}:
            raise ValueError("Upstream setup requires Git or pinned path packages")
        name = entry.get("name")
        directory_name = name.strip("«»") if isinstance(name, str) else ""
        if not re.fullmatch(r"[A-Za-z0-9_.-]+", directory_name) or directory_name in {".", ".."}:
            raise ValueError("Upstream setup requires simple package directory names")
        target = _relative(entry.get("dir")) if entry["type"] == "path" else packages_dir / directory_name
        if entry.get("subDir") is not None:
            _relative(entry["subDir"])
        if any(target == previous or target.is_relative_to(previous) or previous.is_relative_to(target)
               for previous, _ in packages):
            raise ValueError("Upstream package source directories overlap")
        packages.append((target, coordinate({"url": entry.get("url"), "rev": entry.get("rev")})))
    if source is None and not any(value == expected for _, value in packages):
        raise ValueError("Generated Putnam root requires its pinned Mathlib package")
    return source, packages


def _git(arguments: list[str]) -> str:
    # Public upstreams never use ambient URL rewrites, credential helpers, hooks,
    # prompts or authentication settings from the operator's Git configuration.
    environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL="/dev/null",
                       GIT_TERMINAL_PROMPT="0", GIT_ASKPASS="/bin/false")
    result = subprocess.run(["git", "-c", "credential.helper=", "-c", "core.hooksPath=/dev/null", *arguments],
                            env=environment, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Pinned source Git operation failed: {' '.join(arguments)}\n{result.stdout[-4000:]}")
    return result.stdout.strip()


def _fetch(repository: Path, source: dict) -> None:
    _git(["init", "--bare", str(repository)])
    _git(["--git-dir", str(repository), "fetch", "--no-tags", "--depth=1", source["url"], source["rev"]])
    if _git(["--git-dir", str(repository), "rev-parse", "FETCH_HEAD^{commit}"]) != source["rev"]:
        raise ValueError("Fetched source does not match its pinned commit")
    _git(["--git-dir", str(repository), "update-ref", "refs/heads/pinned", source["rev"]])
    _git(["--git-dir", str(repository), "symbolic-ref", "HEAD", "refs/heads/pinned"])


def _cached_source(source: dict, cache_dir: Path) -> Path:
    identity = {"schema_version": 1, **coordinate(source)}
    key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    cache_dir = Path(cache_dir).resolve()
    cache_dir.mkdir(parents=True, exist_ok=True)
    locks = cache_dir / ".locks"
    locks.mkdir(exist_ok=True)
    repository = cache_dir / key
    with (locks / (key + ".lock")).open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        marker = repository / ".lrh-source.json"
        if repository.exists() or repository.is_symlink():
            if (repository.is_symlink() or not repository.is_dir() or not marker.is_file()
                    or marker.is_symlink() or json.loads(marker.read_text()) != identity):
                raise ValueError(f"Refusing to replace an unmanaged source cache: {repository}")
        else:
            with tempfile.TemporaryDirectory(prefix=".fetch-", dir=cache_dir) as temporary:
                staged = Path(temporary) / "repository"
                print(f"Fetching source {source['url']}@{source['rev']}", file=sys.stderr, flush=True)
                _fetch(staged, source)
                (staged / ".lrh-source.json").write_text(json.dumps(identity, sort_keys=True) + "\n")
                staged.rename(repository)
        if _git(["--git-dir", str(repository), "rev-parse", "refs/heads/pinned^{commit}"]) != source["rev"]:
            raise ValueError("Cached source differs from its pinned commit")
    return repository


def checkout(source: dict, destination: Path, cache_dir: Path) -> None:
    """Copy a cached pinned commit into an independent native Git checkout."""
    source = coordinate(source)
    if destination.exists() or destination.is_symlink():
        raise ValueError(f"Source checkout destination already exists: {destination}")
    repository = _cached_source(source, cache_dir)
    destination.parent.mkdir(parents=True, exist_ok=True)
    _git(["clone", "--no-hardlinks", "--no-checkout", "--", str(repository), str(destination)])
    _git(["-C", str(destination), "checkout", "--detach", source["rev"]])
    _git(["-C", str(destination), "remote", "set-url", "origin", source["url"]])
    for path in destination.rglob("*"):
        if path.is_symlink() and not path.resolve().is_relative_to(destination.resolve()):
            raise ValueError(f"Upstream source symlink escapes its checkout: {path}")


def materialize(destination: Path, spec: dict, item: dict, cache_dir: Path) -> None:
    """Build one fresh source tree; the caller publishes it after source checks."""
    source, packages = source_plan(spec, item)
    if source is None:
        destination.mkdir()
    else:
        checkout(source, destination, cache_dir)
    for relative, package in packages:
        target = destination.joinpath(*relative.parts)
        if not target.resolve().is_relative_to(destination.resolve()):
            raise ValueError("Upstream package source directory escaped its snapshot")
        checkout(package, target, cache_dir)

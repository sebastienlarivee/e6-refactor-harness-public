#!/usr/bin/env python3
"""Prepare bundled Lean environments and write machine-local run bindings."""
from __future__ import annotations

import argparse
from dataclasses import replace
import json
import os
from pathlib import Path
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def runtime_root() -> Path:
    return Path(os.environ.get("HARNESS_RUNTIME_ROOT", Path.home() / ".local/share/lean-refactor-harness")).expanduser().resolve()


def downloads_root() -> Path:
    return Path(os.environ.get("HARNESS_DOWNLOADS_ROOT", Path.home() / ".cache/lean-refactor-harness")).expanduser().resolve()


def elan_home() -> Path:
    return Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")).expanduser().resolve()


def validate_policy(config) -> None:
    from decimal import Decimal
    if (config.selected_proofs or config.diagnostic_max_passes is not None
            or config.budget_usd != Decimal("2.90")
            or config.budget_policy != "local-actual-cost-v1"
            or config.concurrency != 2 or config.optimizer != "compact"
            or config.openrouter.get("model_id") != "openai/gpt-6.1-sol"
            or config.openrouter.get("provider") != "openai"
            or config.openrouter.get("default_reasoning_effort") != "high"):
        raise ValueError("Submission policy requires every input proof, Sol 6.1 high, compact, concurrency 2, $2.90 per proof, local-actual-cost-v1, and no pass cap")


def bundled_heartbeats(root: Path) -> Path | None:
    """Use optional cached references only for the bundled default input."""
    path = root / "data/benchmark_heartbeats_final.jsonl"
    return path if path.is_file() else None


def validate_assets(root: Path = ROOT, *, config=None) -> dict:
    """Check setup assets and selected input's pinned snapshot coverage offline."""
    from harness.benchmark import load_benchmark
    from harness.config import RunConfig
    from harness.environments import select_snapshots
    from scripts.setup_environments import PACK_FORMAT, load_setup

    root = Path(root).resolve()
    if config is None:
        config = replace(RunConfig.load(root / "configs/submission.toml"),
                         heartbeat_path=bundled_heartbeats(root))
    validate_policy(config)
    manifest = root / "environment-sources/environment-setup.json"
    required = [config.input_path, manifest]
    if config.heartbeat_path is not None:
        required.append(config.heartbeat_path)
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        raise ValueError("Incomplete submission bundle: missing " + ", ".join(missing)
                         + ". Supply the input/reference file or obtain the complete source bundle before setup/run.")
    benchmark = load_benchmark(config.input_path, config.heartbeat_path)
    setup = load_setup(manifest)
    for row in benchmark.rows:
        try:
            selection = select_snapshots(row, setup["requirements"])
            for sid in (selection["primary"], *selection["compatibility"]):
                if sid not in setup["snapshots"]:
                    raise ValueError(f"snapshot {sid} has no supplied source definition")
        except ValueError as error:
            raise ValueError(f"Unsupported input environment for {row['name']}: {error}; "
                             "run only with the supplied prepared snapshot coverage; run does not download environments") from error
    if setup["format"] == PACK_FORMAT:
        for sid, item in setup["snapshots"].items():
            pack = manifest.parent / item["pack"]
            if (pack.is_symlink() or not pack.resolve().is_relative_to(manifest.parent)
                    or not pack.is_file() or pack.stat().st_size == 0):
                raise ValueError(f"Incomplete submission bundle: missing bundled source pack for {sid}: {pack}; obtain the complete organizer bundle")
            if "bytes" in item and pack.stat().st_size != item["bytes"]:
                raise ValueError(f"Bundled source pack size differs for {sid}: {pack}")
    return {"config": config, "benchmark": benchmark, "manifest": manifest, "setup": setup}


def prepare_environments(assets: dict, root: Path, *, runtime: Path, elan: Path, downloads: Path) -> dict:
    from harness.environments import load_environment_map, validate_dependencies, validate_snapshot
    from scripts import setup_environments

    output = root / "environments.local.toml"
    manifest, setup = assets["manifest"], assets["setup"]
    if output.exists():
        # A published map can belong to the operator. Verify it without rewriting
        # either the map or any adopted project; never repair foreign state.
        binding = load_environment_map(output)
        for sid in setup["snapshots"]:
            spec = setup["requirements"]["snapshots"][sid]
            if sid not in binding.paths or binding.requirements["snapshots"].get(sid) != spec:
                raise ValueError(f"Existing {output} does not bind the supplied snapshot {sid}; preserve it and use a fresh checkout or supply matching prepared bindings")
            problem = setup_environments.toolchain_problem(elan, spec)
            if problem:
                raise ValueError(f"Install the supplied exact Lean toolchain {spec['lean_version']} in ELAN_HOME={elan}: {problem}")
            validate_snapshot(binding, sid, elan_home=elan)
            for row in setup_environments.rows_for_snapshot(setup, sid):
                validate_dependencies(row, binding.paths[sid], elan_home=elan)
        return {"status": "reused", "output_map": str(output)}
    # install() verifies exact compiler/source identities, resumes
    # owned incomplete snapshots, and atomically publishes only a complete map.
    try:
        return setup_environments.install(manifest, runtime / "environments", elan, output,
                                          cache_dir=downloads / "mathlib")
    except ValueError as error:
        if "toolchain" in str(error) or "compiler commit" in str(error) or "elan launcher" in str(error):
            raise ValueError(f"Exact Lean toolchains must already be installed in ELAN_HOME={elan}: {error}") from error
        raise


def write_local_config(root: Path, *, codex: Path, elan: Path) -> Path:
    source = root / "configs/submission.toml"
    document = tomllib.loads(source.read_text(encoding="utf-8"))
    document["benchmark"] = {
        "input": str(root / "data/benchmark_data_final.jsonl"),
        "env_map": str(root / "environments.local.toml"),
    }
    references = bundled_heartbeats(root)
    if references is not None:
        document["benchmark"]["heartbeats"] = str(references)
    document["runtime"] = {"codex": str(codex), "elan_home": str(elan)}
    document["openrouter"]["profile"] = str((source.parent / document["openrouter"]["profile"]).resolve())
    lines = ["# Generated by ./setup.sh; credentials remain in a host-only key file.",
             "schema_version = 1", ""]
    for section, entries in document.items():
        if section == "schema_version":
            continue
        lines.append(f"[{section}]")
        lines.extend(f"{key} = {json.dumps(value)}" for key, value in entries.items())
        lines.append("")
    text = "\n".join(lines)
    output = root / "configs/run.local.toml"
    if output.exists() and output.read_text(encoding="utf-8") == text:
        return output
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", prefix=".run.local.",
                                     suffix=".part", dir=output.parent, delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(text)
    try:
        temporary.replace(output)
    finally:
        temporary.unlink(missing_ok=True)
    return output


def setup(root: Path = ROOT, *, codex: Path | None = None) -> dict:
    root = Path(root).resolve()
    assets = validate_assets(root)
    runtime, elan, downloads = runtime_root(), elan_home(), downloads_root()
    environments = prepare_environments(assets, root, runtime=runtime, elan=elan, downloads=downloads)
    config = write_local_config(root, codex=Path(codex).expanduser().resolve() if codex else runtime / "bin/codex", elan=elan)
    return {"status": "ready", "config": str(config), "environments": environments,
            "next": "./run.sh --api-key-file /absolute/host-only/key-file"}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-assets", action="store_true")
    parser.add_argument("--codex", type=Path)
    args = parser.parse_args(argv)
    try:
        result = {"status": "assets_ready", "proofs": len(validate_assets()["benchmark"].rows)} if args.check_assets else setup(codex=args.codex)
    except (OSError, ValueError, RuntimeError) as error:
        print(f"Setup failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Run every selected input row under the fixed policy and validate its export."""
from __future__ import annotations

import argparse
from dataclasses import replace
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from e6.signals import with_termination_cleanup
from harness import runner
from harness.config import RunConfig
from scripts.monitor import export_retry_command, process_start_tick
from scripts.setup_submission import validate_assets


def default_output() -> Path:
    state = Path(os.environ.get("XDG_STATE_HOME", Path.home() / ".local/state")).expanduser()
    return (state / "lean-refactor-harness/final").resolve()


def run_submission(api_key_file: Path, *, output: Path | None = None,
                   resume: bool = False, input_path: Path | None = None,
                   heartbeat_path: Path | None = None, exclusive_run_key: bool = False,
                   root: Path = ROOT) -> int:
    root = Path(root).resolve()
    output = Path(output).expanduser().resolve() if output is not None else default_output()
    if resume:
        snapshot = runner.load_snapshot(output)
        config = RunConfig.from_frozen_dict(snapshot["config"])
        if exclusive_run_key and config.recovery_policy != "exclusive-key-v1":
            raise ValueError("--exclusive-run-key cannot change the frozen recovery policy on resume")
        for flag, requested, frozen in (("--input", input_path, config.input_path),
                                        ("--heartbeats", heartbeat_path, config.heartbeat_path)):
            if requested is not None and Path(requested).expanduser().resolve() != frozen:
                raise ValueError(f"{flag} cannot change the frozen input/reference on resume; start a fresh output directory")
    else:
        local = root / "configs/run.local.toml"
        if not local.is_file():
            raise ValueError("Submission is not set up: run ./setup.sh first to create configs/run.local.toml")
        config = RunConfig.load(local)
        if exclusive_run_key:
            config = replace(config, recovery_policy="exclusive-key-v1")
        if input_path is not None:
            # A different input must never silently inherit the default references.
            config = replace(config, input_path=input_path, heartbeat_path=heartbeat_path)
        elif heartbeat_path is not None:
            config = replace(config, heartbeat_path=heartbeat_path)
    assets = validate_assets(root, config=config)
    print(f"Run output: {output}", flush=True)
    print(f"Submission: {output / 'submission.jsonl'}", flush=True)
    names = {row["name"] for row in assets["benchmark"].rows}
    if not resume:
        try:
            snapshot = runner.prepare_run(config, output)
        except BaseException as error:
            if (output / "resolved-config.json").is_file():
                raise
            advice = (f"Preflight did not finish in {output}; preserve its evidence and choose a fresh "
                      "--output directory after resolving the failure. No frozen snapshot is available for --resume.")
            if isinstance(error, (KeyboardInterrupt, SystemExit)):
                print(advice, file=sys.stderr, flush=True)
                raise
            raise RuntimeError(f"{error}\n{advice}") from error
    if len(snapshot["proofs"]) != len(names) or {item["task_id"] for item in snapshot["proofs"]} != names:
        raise ValueError(f"{'Frozen' if resume else 'Prepared'} submission must contain all {len(names)} unique selected input names")
    # runner owns mode-0600 key verification, host-only path checks, immutable
    # credential binding, and reuse of every frozen per-proof cost ledger.
    result = runner.run(output, api_key_file=Path(api_key_file).expanduser().resolve(), resume=resume)
    if result != 0:
        return result
    if runner.status(output).get("status") != "completed":
        raise RuntimeError("Run did not complete; inspect status and use --resume before export")
    from harness.export import export_run
    publication = {"schema_version": 1, "run_identity": snapshot["identity"],
                   "status": "exporting", "pid": os.getpid(),
                   "process_start_tick": process_start_tick(os.getpid())}
    runner.write(output / "submission-status.json", publication)
    print("Proof work completed; independently validating the submission export.", flush=True)
    try:
        receipt = export_run(output, output / "submission.jsonl")
    except BaseException as error:
        interrupted = isinstance(error, (KeyboardInterrupt, SystemExit))
        publication.update(status="export_interrupted" if interrupted else "export_failed", error=str(error))
        runner.write(output / "submission-status.json", publication)
        advice = ("Proof progress and spending ledgers are preserved. Retry export without inference:\n"
                  + export_retry_command(output, release_root=root))
        if interrupted:
            print(advice, file=sys.stderr, flush=True)
            raise
        raise RuntimeError(f"Submission export failed: {error}\n{advice}") from error
    publication.update(status=receipt["status"], output=str(output / "submission.jsonl"))
    runner.write(output / "submission-status.json", publication)
    print(json.dumps(receipt, indent=2, default=str))
    return 0


@with_termination_cleanup
def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--api-key-file", type=Path, required=True,
                        help="Absolute path to a host-only mode-0600 ordinary OpenRouter key file")
    parser.add_argument("--output", type=Path, help="Absolute run directory (must be outside this checkout)")
    parser.add_argument("--input", type=Path, help="Absolute benchmark JSONL path; defaults to the bundled final input")
    parser.add_argument("--heartbeats", type=Path, help="Optional absolute heartbeat-reference JSONL path; missing references are measured before spending")
    parser.add_argument("--resume", action="store_true", help="Continue the same frozen run and cost ledgers")
    parser.add_argument("--exclusive-run-key", action="store_true",
                        help="Assert this key is used only by this run; allow one audited presumed-zero recovery")
    args = parser.parse_args(argv)
    if any(path is not None and not path.is_absolute()
           for path in (args.api_key_file, args.output, args.input, args.heartbeats)):
        parser.error("--api-key-file, --output, --input and --heartbeats must be absolute paths")
    try:
        return run_submission(args.api_key_file, output=args.output, resume=args.resume,
                              input_path=args.input, heartbeat_path=args.heartbeats,
                              exclusive_run_key=args.exclusive_run_key)
    except (OSError, ValueError, RuntimeError) as error:
        print(f"Submission failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

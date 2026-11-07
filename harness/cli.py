"""Submission-facing commands; the internal research CLI is not a public workflow."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

from .config import RunConfig
from . import runner
from e6.signals import with_termination_cleanup


def _json(value):
    print(json.dumps(value, indent=2, ensure_ascii=False, default=str))


def _config_arguments(parser):
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--input", dest="input_path", type=Path)
    parser.add_argument("--heartbeats", dest="heartbeat_path", type=Path)
    parser.add_argument("--env-map", type=Path)
    parser.add_argument("--concurrency", type=int, choices=(1, 2))
    parser.add_argument("--optimizer", choices=("compact", "off"))
    parser.add_argument("--proof", dest="selected_proofs", action="append")
    parser.add_argument("--diagnostic-max-passes", type=int)
    parser.add_argument("--exclusive-run-key", action="store_true",
        help="Assert the ordinary key is used only by this run; freeze exclusive-key-v1 recovery")


def _load(args):
    overrides = {name: getattr(args, name, None) for name in ("input_path", "heartbeat_path", "env_map", "concurrency", "optimizer", "selected_proofs", "diagnostic_max_passes")}
    if getattr(args, "exclusive_run_key", False):
        overrides["recovery_policy"] = "exclusive-key-v1"
    return RunConfig.load(args.config, **overrides)


def _auth_arguments(parser, *, internal=False):
    parser.set_defaults(key_store=None)
    if internal:
        auth = parser.add_mutually_exclusive_group(required=True)
        auth.add_argument("--api-key-file", type=Path)
        auth.add_argument("--key-store", type=Path)
    else:
        parser.add_argument("--api-key-file", type=Path, required=True,
            help="Host-only ordinary OpenRouter key shared by independent proof ledgers")


@with_termination_cleanup
def main(argv=None):
    parser = argparse.ArgumentParser(prog="harness", description="e6: Lean proof refactoring with frozen OpenRouter budgets")
    sub = parser.add_subparsers(dest="command", required=True)
    setup = sub.add_parser("setup", help="Install pinned local runtime")
    setup.add_argument("--dev", action="store_true")
    setup.add_argument("--codex", type=Path)
    doctor = sub.add_parser("doctor", help="Verify paths, snapshots, original proofs and native tools before spending")
    _config_arguments(doctor)
    doctor.add_argument("--quick", action="store_true")
    doctor.add_argument("--output", type=Path)
    prepare = sub.add_parser("prepare", help="Freeze a fresh run without inference; publish stable proof budget identities")
    _config_arguments(prepare)
    prepare.add_argument("--output", type=Path, required=True)
    run = sub.add_parser("run", help="Prepare or execute a frozen run")
    _config_arguments(run)
    run.add_argument("--output", type=Path, required=True)
    _auth_arguments(run)
    status = sub.add_parser("status", help="Read progress and preserved partial results")
    status.add_argument("root", type=Path)
    resume = sub.add_parser("resume", help="Continue using the exact frozen configuration and original proof ledgers")
    resume.add_argument("root", type=Path)
    _auth_arguments(resume)
    export = sub.add_parser("export", help="Write contest name/proof JSONL with verified best or original fallback")
    export.add_argument("root", type=Path)
    export.add_argument("--output", type=Path, required=True)
    worker = sub.add_parser("_proof", help=argparse.SUPPRESS)
    worker.add_argument("root", type=Path)
    worker.add_argument("label")
    worker.add_argument("--resume", action="store_true")
    _auth_arguments(worker, internal=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "setup":
            script = Path(__file__).resolve().parents[1] / "setup.sh"
            arguments = ["--dev"] if args.dev else []
            if args.codex:
                arguments.extend(["--codex", str(args.codex)])
            return subprocess.run(["bash", str(script), *arguments], check=False).returncode
        if args.command == "doctor":
            from .doctor import check
            report = check(_load(args), quick=args.quick, output_dir=args.output)
            _json(report)
            return int(report.get("status") not in {"passed", "ready", "ok"})
        if args.command == "prepare":
            snapshot = runner.prepare_run(_load(args), args.output)
            _json({"root": snapshot["root"], "identity": snapshot["identity"], "proofs": {
                item["label"]: runner.proof_identity(snapshot, item) for item in snapshot["proofs"]}})
            return 0
        if args.command == "run":
            config = _load(args)
            if not (args.output / "resolved-config.json").exists():
                runner.prepare_run(config, args.output)
            elif runner.load_snapshot(args.output)["config"] != config.to_dict():
                raise ValueError("Requested configuration differs from the prepared run")
            return runner.run(args.output, key_store=args.key_store, api_key_file=args.api_key_file)
        if args.command == "resume":
            return runner.run(args.root, key_store=args.key_store, api_key_file=args.api_key_file, resume=True)
        if args.command == "status":
            _json(runner.status(args.root))
            return 0
        if args.command == "export":
            from .export import export_run
            _json(export_run(args.root, args.output))
            return 0
        if args.command == "_proof":
            return runner.run_proof(args.root, args.label, key_store=args.key_store,
                api_key_file=args.api_key_file, resume=args.resume)
    except (ValueError, RuntimeError, OSError) as error:
        print(f"harness: {error}", file=sys.stderr)
        return 2
    return 0

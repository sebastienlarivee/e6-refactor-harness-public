# Run and collect results

After [setup](setup.md), save a funded OpenRouter API key in a private host file outside the release, run directory and prepared Lean projects. Set its permissions with `chmod 600 /absolute/private/openrouter.key`. The account needs access to the supplied OpenRouter route.

## Start and monitor

```sh
nohup ./run.sh --api-key-file /absolute/private/openrouter.key \
  --output "$HOME/lean-refactor-run" > run.log 2>&1 < /dev/null &
tail -n 40 run.log
.venv/bin/python scripts/monitor.py --root "$HOME/lean-refactor-run"
```

Choose a fresh output directory outside the release. If `--output` is omitted, the default is `${XDG_STATE_HOME:-$HOME/.local/state}/lean-refactor-harness/final`; the launcher prints the resolved path. Monitoring is read-only. Keep one launcher per run directory.

The launcher runs every input row with the included Sol 6.1 high policy, two concurrent proofs and compact optimization. It preserves independently verified improvements and automatically exports `submission.jsonl` when execution completes.

During the initial checks, the monitor shows `Original proofs checked: N/T` for the input set. It then shows theorem names and proof progress, followed by `exporting` during final validation and `submission ready` when the output matches its export report. If export needs attention, it prints the failure and a command using a fresh output filename.

## Inputs and baselines

The default input is `data/benchmark_data_final.jsonl`, containing all 60 final benchmark rows. To run a subset, copy the desired complete rows unchanged into another JSONL and use a fresh output directory:

```sh
./run.sh --api-key-file /absolute/private/openrouter.key \
  --input /absolute/subset.jsonl --output "$HOME/e6-subset-run"
```

Every row in the supplied JSONL runs. Keep names unique and preserve each complete input row. Subsets of the bundled 60 use the already prepared environments. Add `--heartbeats /absolute/references.jsonl` to supply all or some heartbeat references for your input; missing references are measured during preflight. Unknown snapshots or missing compiled dependencies fail before inference.

Supplied `proof_length` and heartbeat references remain the scoring denominators. When either is absent, preflight derives it from the original proof using the same token or native heartbeat measurement convention as candidate validation. Each proof's baseline receipt records the values, their supplied or measured provenance, original source and environment identity. These references are frozen before spending and reused by workers and resume.

## Resume after an interruption

Once the previous launcher has stopped, continue the same output directory with the same key:

```sh
nohup ./run.sh --resume --api-key-file /absolute/private/openrouter.key \
  --output "$HOME/lean-refactor-run" > resume.log 2>&1 < /dev/null &
```

Resume keeps the existing configuration, baseline receipts, proof progress and remaining budgets. Use the same release, input/reference files, runtime, projects, key and run paths. The frozen configuration supplies the original input/reference paths automatically.

If preparation failed before `resolved-config.json` was written, no inference started and there is no frozen run to resume. Fix the reported setup/input issue, preserve the failed directory for its diagnostics, and retry with a fresh `--output` directory. If only export failed, use [export recovery](#result-and-export-recovery) instead.

## Spending

Each proof has its own actual-cost ledger and USD 2.90 spending threshold, even when two proofs share one ordinary key. The threshold leaves a USD 0.10 buffer for the final request; all 60 submitted proof attempts stayed below the contest's USD 3 cap. Reported cache discounts count, and separately billed BYOK upstream inference counts as spend.

An unresolved charge normally blocks spending for that proof while receipt recovery runs. Resume preserves charges, unresolved liability, and the frozen recovery policy. Keep the original ledgers and key, and inspect the retained logs and reports if recovery needs attention.

## Automatic recovery

New runs save OpenRouter's generation ID as soon as response headers arrive. A request that demonstrably failed before being sent can retry. When a stream loses its final bill, the harness polls the generation endpoint with bounded backoff. Proofs awaiting billing are revisited after the other workers finish and may resume once automatically, retaining their verified candidate, remaining budget and frozen execution policy.

For the rare request with no generation ID or observed output, use one regular API key exclusively for this run and add this flag when starting it:

```sh
./run.sh --exclusive-run-key --api-key-file /absolute/private/openrouter.key \
  --output "$HOME/lean-refactor-run"
```

The flag asserts that this run has exclusive use of the key. It enables at most one presumed-zero recovery across the run, only when exactly one charge is unknown. The harness records starting usage before inference, waits until all workers have stopped, allows at least five minutes after the failed attempt, and requires three matching usage readings thirty seconds apart. Both OpenRouter charges and BYOK usage must reconcile exactly with known receipts. Discrepancies, incomplete evidence, or additional unknown charges leave the proof blocked.

This recovery is an explicit accounting assumption, not a provider-confirmed free request. The original attempt and its unknown cost remain in the ledger, alongside the audit evidence in `recovery/`. A later authoritative bill can still be recorded; a later unexplained usage discrepancy revokes the assumption and blocks further spending for that proof. The audit runs again at the next idle checkpoint and on resume. Exports keep provisional costs marked as unresolved.

For keys shared elsewhere, use the default generation-receipt recovery. Resume automatically uses the policy chosen when the run started.

## Result and export recovery

The output directory contains `submission.jsonl`, its adjacent `.report.json`, and independent Lean validation evidence in `.evidence/`. The JSONL contains full declarations under `name` and `proof`; export retains a checked original when an eligible improved checkpoint is unavailable. Review report failures, original fallbacks and cost accounting before submitting.

If execution has stopped but automatic export failed, preserve its evidence and retry to a fresh filename:

```sh
.venv/bin/harness export "$HOME/lean-refactor-run" \
  --output "$HOME/lean-refactor-run/submission-retry.jsonl"
```

Export independently validates the saved results without further inference. Upload the completed JSONL through the organizer's submission channel; it must contain every selected input name exactly once.

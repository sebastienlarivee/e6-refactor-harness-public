# e6

by Sebastien Larivee for the [Lean Refactor Arena](https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena) competition

e6 refactors Lean proofs using Sol 6.1 high, Lean feedback and compact optimization. The default run processes all 60 final benchmark proofs, with two proofs running concurrently.

## Set up

Use Linux x86_64 with Python 3.12+ and the benchmark's Lean toolchains installed through native elan. See [host prerequisites](docs/setup.md#prerequisites). Extract the release onto a Linux filesystem, then run:

```sh
./setup.sh
```

Setup installs Python dependencies and the pinned Codex CLI, downloads the pinned Lean project sources, prepares their compiled dependencies using caches or source builds, and writes the machine configuration. It needs network access. If elan is outside `~/.elan`, use `ELAN_HOME=/absolute/elan-home ./setup.sh`. See [setup details](docs/setup.md).

## Run the benchmark

Save a funded OpenRouter API key in a private file outside the release and run directory, with permissions `0600`. Then start the run in the background:

```sh
nohup ./run.sh --api-key-file /absolute/private/openrouter.key \
  --output "$HOME/lean-refactor-run" > run.log 2>&1 < /dev/null &
```

The launcher checks the originals, prepares any missing baseline references, runs every input proof and automatically exports the verified result when execution completes. The initial checks can take an hour or more for the full set; the monitor shows how many originals have been checked. Confirm startup and monitor progress:

```sh
tail -n 40 run.log
.venv/bin/python scripts/monitor.py --root "$HOME/lean-refactor-run"
```

Provider receipt recovery is automatic. See [operations](docs/operations.md) for interruption recovery and the optional exclusive-key recovery mode.

Each proof uses a USD 2.90 spending threshold to leave a USD 0.10 buffer for the final request. All 60 submitted proof attempts stayed below the contest's USD 3 cap. See [accounting details](docs/operations.md#spending) for receipt handling and interrupted requests.

## Run a subset

Create a JSONL containing any subset of the rows in `data/benchmark_data_final.jsonl`, keeping each selected row unchanged. Pass its absolute path and a fresh output directory:

```sh
./run.sh --api-key-file /absolute/private/openrouter.key \
  --input /absolute/subset.jsonl --output "$HOME/e6-subset-run"
```

Every row in that file runs under the same policy using the prepared environments. Optional heartbeat references and their measurement are described in [inputs and baselines](docs/operations.md#inputs-and-baselines).

## Collect the result

When the monitor shows `submission ready`, review `submission.jsonl.report.json` in `$HOME/lean-refactor-run`. Upload that directory's `submission.jsonl` through the organizer's submission channel. It contains one full `name`/`proof` declaration for every input row.

If execution is interrupted, [resume the same run](docs/operations.md#resume-after-an-interruption) with its original key. Keep the release, installed environments and run directory unchanged until export is complete.

## Agent execution

- Each pass uses a fresh Codex home and ephemeral session, with ambient user configuration and rules disabled.
- Shell commands run through bubblewrap with read-only project/toolchain mounts and a writable pass workspace.
- Agents work from the supplied original proof and, on later passes, that proof's verified incumbent from the current run.
- Host workers hold the OpenRouter key and provide proof-specific model relay access. Final exports receive independent Lean validation.

## Publication snapshot

This source snapshot is based on the submitted harness at revision `735528fea1dbf2a1c400a58b2f2e65e19422d811`. Publication cleanup removes machine-specific paths from historical baseline metadata and adds licensing and packaging notices. The refactoring implementation, prompts, benchmark rows, model configuration, and optimizer settings are unchanged.

The cleanup changes the frozen source identity. Use this copy for fresh runs; resume existing submitted runs with their original release.

## License

Original harness code is licensed under [MIT](LICENSE). Bundled third-party code and benchmark material retain their upstream licenses; see [third-party notices](THIRD_PARTY_NOTICES.md).

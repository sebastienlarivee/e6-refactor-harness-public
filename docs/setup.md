# Setup

The release contains the default input, model configuration and an environment manifest specifying exact upstream source commits. Setup downloads the project and dependency sources, prepares their compiled dependencies on your machine, and writes the local configuration.

## Prerequisites

- Native Linux x86_64, including WSL2 Ubuntu, with Python 3.12 or newer.
- Bash, Git, bubblewrap (`bwrap`), curl, tar, `/usr/bin/nice` and ordinary Linux utilities.
- Working unprivileged user/mount namespaces for proof isolation.
- Native elan with all exact Lean toolchains required by the supplied environment manifest already installed, including standard-library sources and headers.
- Writable Linux storage with executable files, symlinks and POSIX permissions, plus network access for uncached runtime/package/compiled-cache downloads.

The benchmark's Lean toolchains are assumed to be available. Setup checks their exact versions and compiler identities. Run the commands below in a Linux shell.

For Ubuntu 24.04, install any missing host packages with:

```sh
sudo apt-get update
sudo apt-get install python3 python3-venv git bubblewrap curl tar unzip
```

On other distributions, install the equivalent packages and ensure Python is at least 3.12. Setup checks bubblewrap's namespace support before installing the runtime or preparing projects.

## Install

Extract the supplied ZIP onto Linux storage and run from its `lean-refactor-harness` directory:

```sh
./setup.sh
```

Setup installs the locked Python dependencies and Codex CLI 0.164.0. It then fetches the exact project and dependency commits from GitHub, applies the supplied project configuration, downloads matching compiled caches when available, and builds missing required imports. Each benchmark version has its own project directory. Setup writes `environments.local.toml` plus `configs/run.local.toml` when preparation is complete.

The default elan home is `~/.elan`. For an existing installation elsewhere:

```sh
ELAN_HOME=/absolute/elan-home ./setup.sh
```

The default Codex runtime and prepared projects are under `~/.local/share/lean-refactor-harness`. `HARNESS_RUNTIME_ROOT` selects another location; `./setup.sh --codex /absolute/native/bin/codex` reuses an existing pinned executable. Setup records the resulting paths automatically.

Downloads and the Mathlib cache default to `~/.cache/lean-refactor-harness`; set `HARNESS_DOWNLOADS_ROOT` to change that location. The Mathlib cache can contain executable helper tools, so keep this location, the runtime, projects and run data on a Linux filesystem. Allow space for all benchmark versions concurrently.

Fetched Git objects are cached separately for reuse across project versions and retries. `HARNESS_SOURCE_CACHE_ROOT` selects an external location for this source-download cache, including suitable exFAT storage. The prepared projects and compiled caches stay on Linux storage.

If setup is interrupted, rerun the same command with the same paths. Completed source downloads and owned project preparation are reused. Keep setup output and each project's `.lrh-setup-commands.jsonl` if a build fails. The default input and environment manifest are required; a heartbeat reference file is optional.

## After setup

Run `./run.sh` as shown in the [README](../README.md). Its preflight verifies tooling, environment identities, compiled imports and every original proof, then freezes the baseline measurements before model spending. An alternative `--input` uses the snapshots and compiled imports prepared by setup. Keep the extracted release and prepared environments unchanged during execution, resume and export.

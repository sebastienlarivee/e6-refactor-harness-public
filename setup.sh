#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
dev=0
codex=""
runtime_only=0
while (($#)); do
  case "$1" in
    --dev) dev=1; shift ;;
    --codex) [[ $# -ge 2 ]] || { echo "--codex requires a path" >&2; exit 2; }; codex="$2"; shift 2 ;;
    --runtime-only) runtime_only=1; shift ;;
    --help|-h) echo "Usage: ./setup.sh [--dev] [--codex /absolute/path/to/codex]"; exit 0 ;;
    *) echo "Unknown option: $1" >&2; exit 2 ;;
  esac
done
[[ "$(uname -s)" == Linux && "$(uname -m)" == x86_64 ]] || { echo "This release requires Linux x86_64 (WSL2 Ubuntu is supported)." >&2; exit 1; }
python="${HARNESS_PYTHON:-python3}"
"$python" -c 'import sys; assert sys.version_info >= (3,12), "Python 3.12 or newer is required"'
if ((!runtime_only)); then
  "$python" scripts/setup_submission.py --check-assets
fi
for command in git bwrap curl tar; do
  command -v "$command" >/dev/null || { echo "Missing $command; install it using your system package manager." >&2; exit 1; }
done
[[ -x /usr/bin/nice ]] || { echo "Missing /usr/bin/nice; install coreutils using your system package manager." >&2; exit 1; }
if ! bwrap --die-with-parent --unshare-user --ro-bind / / /bin/true; then
  echo "Bubblewrap requires working unprivileged user/mount namespaces. Enable them or use a supported Linux host before setup." >&2
  exit 1
fi
if [[ -n "${HARNESS_UV:-}" ]]; then
  uv_bin="$HARNESS_UV"
  [[ -x "$uv_bin" ]] || { echo "HARNESS_UV must name an executable uv installation." >&2; exit 1; }
elif command -v uv >/dev/null; then
  uv_bin="$(command -v uv)"
elif [[ -x "$HOME/.local/bin/uv" ]]; then
  uv_bin="$HOME/.local/bin/uv"
else
  "$python" -m venv .bootstrap
  .bootstrap/bin/python -m pip install 'uv==0.11.15'
  uv_bin="$PWD/.bootstrap/bin/uv"
fi
if ((dev)); then
  "$uv_bin" sync --frozen --extra dev
else
  "$uv_bin" sync --frozen --no-dev
fi
if [[ -n "$codex" ]]; then
  [[ "$codex" == /* && -x "$codex" ]] || { echo "--codex must be an absolute executable path." >&2; exit 1; }
  [[ "$("$codex" --version)" == "codex-cli 0.164.0" ]] || { echo "Codex CLI 0.164.0 is required." >&2; exit 1; }
  printf 'Using existing Codex: %s\n' "$codex"
else
  .venv/bin/python scripts/setup_runtime.py --runtime "${HARNESS_RUNTIME_ROOT:-$HOME/.local/share/lean-refactor-harness}" --downloads "${HARNESS_DOWNLOADS_ROOT:-$HOME/.cache/lean-refactor-harness}"
fi
if ((runtime_only)); then
  echo "Developer runtime setup complete; submission environments and configuration were not prepared."
elif [[ -n "$codex" ]]; then
  .venv/bin/python scripts/setup_submission.py --codex "$codex"
else
  .venv/bin/python scripts/setup_submission.py
fi

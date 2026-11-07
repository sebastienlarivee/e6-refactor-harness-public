"""Reap detached tools when a native proof CLI exits, without a PID namespace.

This trusted host process has exactly one CLI subtree. Linux reparents orphaned
descendants here, so their original leader may exit before cleanup begins.
"""
from __future__ import annotations

import ctypes
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def _children() -> list[int]:
    result = []
    for path in Path('/proc').glob('[0-9]*/stat'):
        try:
            # A Linux command name can contain spaces and closing parentheses.
            fields = path.read_text().rsplit(')', 1)[1].split()
            if int(fields[1]) == os.getpid():
                result.append(int(path.parent.name))
        except (OSError, IndexError, ValueError):
            continue
    return result


def _reap_all() -> None:
    deadline = time.monotonic() + 10
    while True:
        # Killing an adopted child reparents its descendants here as well.
        for pid in _children():
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        try:
            while os.waitpid(-1, os.WNOHANG)[0]:
                pass
        except ChildProcessError:
            return
        if time.monotonic() >= deadline:
            raise RuntimeError('Native CLI descendants could not be reaped')
        time.sleep(0.01)


def main(argv: list[str]) -> int:
    if not argv or argv[0] != '--' or len(argv) < 2:
        raise ValueError('Expected -- followed by the native CLI wrapper command')
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER
        raise OSError(ctypes.get_errno(), 'Could not supervise native CLI descendants')
    process = subprocess.Popen(argv[1:])

    def interrupted(signum, frame):
        del frame
        raise InterruptedError(f'Native CLI supervisor received signal {signum}')

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        code = process.wait()
    finally:
        _reap_all()
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    try:
        raise SystemExit(main(sys.argv[1:]))
    except (OSError, RuntimeError, ValueError) as error:
        print(f'E6 native supervisor: {error}', file=sys.stderr)
        raise SystemExit(70)

"""Make command-line termination unwind the controller's owned-process cleanup."""
from __future__ import annotations

from contextlib import contextmanager
from functools import wraps
import signal
import threading


@contextmanager
def termination_cleanup():
    """Translate termination once, then let finally blocks finish without reentry.

    A CLI can own detached proof cells, so SIGTERM must not bypass its finally
    blocks. Restore the caller's handlers after an embedded main() invocation.
    Library calls from another thread cannot install process signal handlers.
    """
    if threading.current_thread() is not threading.main_thread():
        yield
        return
    received = False

    def interrupted(signum, frame):
        nonlocal received
        if not received:
            received = True
            raise KeyboardInterrupt(f"Controller received signal {signum}")

    previous = {}
    try:
        for signum in (signal.SIGTERM, signal.SIGINT,
                       *([signal.SIGBREAK] if hasattr(signal, "SIGBREAK") else [])):
            previous[signum] = signal.signal(signum, interrupted)
        yield
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def with_termination_cleanup(main):
    @wraps(main)
    def wrapped(*args, **kwargs):
        with termination_cleanup():
            return main(*args, **kwargs)
    return wrapped


@contextmanager
def defer_termination():
    """Register a newly spawned child before a Python interrupt can unwind.

    Do not use pthread_sigmask here: children inherit its blocked signal mask.
    This very short scope changes only installed Python handlers, and replays
    the first interruption after ownership has been registered.
    """
    if threading.current_thread() is not threading.main_thread():
        yield
        return
    previous, pending = {}, []

    def deferred(signum, frame):
        if not pending:
            pending.append((signum, frame))

    try:
        for signum in (signal.SIGTERM, signal.SIGINT,
                       *([signal.SIGBREAK] if hasattr(signal, "SIGBREAK") else [])):
            handler = signal.getsignal(signum)
            if callable(handler):
                previous[signum] = handler
                signal.signal(signum, deferred)
        yield
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)
        if pending:
            signum, frame = pending[0]
            previous[signum](signum, frame)

"""Bounded tactic-kind accounting for Lean's native Firefox timing export.

Lean 4.26 can attach message-generation traces outside their parent's timed body.
Signed slices are usable only when their cancellation stays inside a contiguous
run carrying one identical output label. They are never clamped or sorted.
"""
from __future__ import annotations

from contextlib import closing
from itertools import groupby
import math
from pathlib import Path
from typing import Any, Callable, Iterator, NoReturn

from lean_tools import native_profile_json


# Native timestamps and weights are milliseconds from a nanosecond clock.
# Allow one nanosecond for independently serialized Float endpoints/differences.
TIME_TOLERANCE_MS = 0.000001
DEFAULT_MAX_PROFILE_BYTES = 256 * 1024 * 1024
DEFAULT_MAX_SAMPLES = 8_000_000
DEFAULT_MAX_PARSE_SECONDS = native_profile_json.MAX_PARSE_SECONDS


def _finite(value: Any) -> bool:
    try:
        return type(value) in (int, float) and math.isfinite(value)
    except OverflowError:
        return False


def _array(table: Any, key: str) -> Any:
    if type(table) is not dict or type(table.get(key)) not in (list, native_profile_json.PackedColumn):
        raise ValueError("unsupported native profile table: " + key)
    return table[key]


def _index(value: Any, entries: list) -> int:
    if type(value) is not int or not 0 <= value < len(entries):
        raise ValueError("invalid native profile table index")
    return value


def _labels(thread: dict[str, Any]) -> list[str | None]:
    stack_frames = _array(thread.get("stackTable"), "frame")
    parents = _array(thread.get("stackTable"), "prefix")
    frame_funcs = _array(thread.get("frameTable"), "func")
    func_names = _array(thread.get("funcTable"), "name")
    strings = _array(thread, "stringArray")
    if len(stack_frames) != len(parents) or any(type(label) is not str for label in strings):
        raise ValueError("unsupported native stack/string table")
    labels: list[str | None] = []
    for index, frame in enumerate(stack_frames):
        func = frame_funcs[_index(frame, frame_funcs)]
        name = func_names[_index(func, func_names)]
        label = strings[_index(name, strings)]
        parent = parents[index]
        if parent is not None and (type(parent) is not int or not 0 <= parent < index):
            raise ValueError("unsupported native stack hierarchy")
        labels.append(label if "Lean.Parser.Tactic." in label else labels[parent] if parent is not None else None)
    return labels


def _iter_signed_runs(sample: dict[str, Any], labels: list[str | None],
                      check: Callable[[], None] | None = None) -> Iterator[tuple[str | None, float]]:
    """Prove each same-label run is one nonnegative interval, then sum its weights.

    Continuity makes the signed differences telescope. Containment prevents an
    excursion from crossing another label's interval. Every check is local to
    one thread; cancellation across labels or threads is never permitted.
    Forward, unattributed zero-weight idle intervals separate runs, so signed
    cancellation cannot bridge their unaccounted elapsed time.
    """
    def reject(reason: str) -> NoReturn:
        raise ValueError("native profile has negative wall-time weights that cannot be safely coalesced: " + reason)

    weights, stacks = sample["weight"], sample["stack"]
    times = sample.get("time", [])
    if sample.get("weightType") != "tracing-ms":
        reject("unsupported signed-slice weight type")
    if type(times) not in (list, native_profile_json.PackedColumn) or len(weights) % 2 or len(times) != len(weights):
        reject("missing paired native timestamps")
    if type(times) is list and any(not _finite(value) for value in times):
        reject("non-finite native timestamp")

    def pairs() -> Iterator[tuple[int, str | None, float, float, float]]:
        run = 0
        previous_label: Any = object()
        for index in range(0, len(weights), 2):
            if check is not None and index % 16384 == 0:
                check()
            first, last = times[index:index + 2]
            weight = weights[index + 1]
            if stacks[index] != stacks[index + 1] or weights[index] != 0:
                reject("invalid native slice pair")
            if index and first != times[index - 1]:
                reject("discontinuous native slice endpoints")
            difference = last - first
            label = labels[stacks[index]]
            if weight == 0 and first != last:
                if label is not None or not _finite(difference) or difference < 0:
                    reject("invalid zero-weight idle interval")
                run += 1
                previous_label = object()
                continue
            if not _finite(difference) or not math.isclose(weight, difference, rel_tol=0, abs_tol=TIME_TOLERANCE_MS):
                reject("native weight disagrees with its timestamp difference")
            if label != previous_label:
                run += 1
            previous_label = label
            yield run, label, first, last, weight

    for _, entries in groupby(pairs(), key=lambda item: item[0]):
        label: str | None = None
        start = stop = minimum = maximum = None

        def parts() -> Iterator[float]:
            nonlocal label, start, stop, minimum, maximum
            for _, label, first, last, weight in entries:
                if start is None:
                    start = first
                    minimum, maximum = min(first, last), max(first, last)
                else:
                    minimum, maximum = min(minimum, first, last), max(maximum, first, last)
                stop = last
                yield weight

        try:
            total = math.fsum(parts())
        except OverflowError:
            reject("non-finite same-label aggregate")
        if not math.isfinite(total):
            reject("non-finite same-label aggregate")
        if start > stop or minimum < start or maximum > stop or total < 0:
            reject("a same-label excursion crosses its interval boundary")
        extent = stop - start
        if not _finite(extent) or not math.isclose(total, extent, rel_tol=0, abs_tol=TIME_TOLERANCE_MS):
            reject("same-label weights do not telescope to their interval")
        yield label, total


def _iter_slices(sample: dict[str, Any], labels: list[str | None],
                 check: Callable[[], None] | None = None) -> tuple[Iterator[tuple[str | None, float]], int]:
    weights, stacks = _array(sample, "weight"), _array(sample, "stack")
    if type(sample.get("length")) is not int or sample["length"] != len(weights) or len(weights) != len(stacks):
        raise ValueError("native sample length mismatch")
    if type(weights) is list and any(not _finite(weight) for weight in weights):
        raise ValueError("native profile has invalid/negative wall-time weights; no unit repair attempted")
    if any(type(stack) is not int or not 0 <= stack < len(labels) for stack in stacks):
        raise ValueError("invalid native sample stack")
    negative = weights.negative_count if isinstance(weights, native_profile_json.PackedColumn) else sum(weight < 0 for weight in weights)
    if negative:
        return _iter_signed_runs(sample, labels, check), negative
    # Positive-only native threads can contain zero-weight idle intervals. Their
    # existing weight accounting is retained; no signed cancellation is needed.
    return ((labels[stack], weight) for stack, weight in zip(stacks, weights)), 0


def _signed_runs(sample: dict[str, Any], labels: list[str | None]) -> tuple[list[tuple[str | None, float]], int]:
    return list(_iter_signed_runs(sample, labels)), sum(weight < 0 for weight in sample['weight'])


def _slices(sample: dict[str, Any], labels: list[str | None]) -> tuple[list[tuple[str | None, float]], int]:
    slices, negative = _iter_slices(sample, labels)
    return list(slices), negative


def summarize(path: Path, top_n: int, *, max_profile_bytes: int, max_samples: int) -> dict[str, Any]:
    def unavailable(note: str) -> dict[str, Any]:
        return {"hotspots": [], "complete": False, "truncated": True, "profile_note": note}

    if path.stat().st_size > max_profile_bytes:
        return unavailable(f"native profile exceeds the {max_profile_bytes} byte parsing bound")
    reader = native_profile_json.ProfileReader(path, max_bytes=max_profile_bytes, max_samples=max_samples)
    totals: dict[str, float] = {}
    total, unattributed, samples = 0.0, 0.0, 0
    coalesced = []
    try:
        with closing(reader.threads()) as threads:
            for thread_index, thread in enumerate(threads):
                sample = thread.get("samples")
                weights = _array(sample, "weight")
                if len(weights) + samples > max_samples:
                    raise native_profile_json.ProfileBudgetExceeded(f"native profile exceeds the {max_samples} sample parsing bound")
                labels = _labels(thread)
                slices, negative_count = _iter_slices(sample, labels, reader.check)
                runs = 0
                for label, weight in slices:
                    runs += 1
                    if runs % 8192 == 0:
                        reader.check()
                    total += weight
                    if label is None:
                        unattributed += weight
                    else:
                        totals[label] = totals.get(label, 0.0) + weight
                    if not all(math.isfinite(value) for value in (total, unattributed, totals.get(label, 0.0))):
                        raise ValueError("native profile has non-finite wall-time aggregate")
                if negative_count:
                    coalesced.append({"thread_index": thread_index, "raw_negative_samples": negative_count,
                                      "validated_same_label_runs": runs})
                samples += len(weights)
                reader.check()
    except native_profile_json.ProfileBudgetExceeded as error:
        return unavailable(str(error))
    units = reader.meta.get("sampleUnits") if type(reader.meta) is dict else None
    if type(units) is not dict or units.get("time") != "ms":
        raise ValueError("unsupported native wall-time units")
    ranked = sorted(totals.items(), key=lambda item: (-item[1], item[0]))
    result = {"hotspots": [{"label": label[:200], "exclusive_slice_milliseconds": round(value, 6),
                            "original_span": None, "mapping_confidence": "unavailable_native_label_only"}
                           for label, value in ranked[:top_n]],
              "boundary": "native runFrontend including imports and prefix", "wall_time_milliseconds": round(total, 6),
              "thread_aggregation": "Sum of native thread slices; may include concurrent work and is not elapsed process wall time.",
              "unattributed_milliseconds": round(unattributed, 6), "samples": samples,
              "grouping": "exclusive slices assigned to nearest enclosing tactic-kind label; repeated kinds grouped",
              "complete": True, "truncated": len(ranked) > top_n,
              "instrumentation_overhead": {"status": "not_separately_measured"}}
    if coalesced:
        result["native_slice_accounting"] = {
            "method": "validated_contiguous_same_label_signed_sums",
            "raw_negative_samples": sum(item["raw_negative_samples"] for item in coalesced),
            "threads": coalesced, "raw_trace_unchanged": True,
            "policy": "Paired timestamp differences telescope within contained, continuous same-label runs; forward unattributed zero-weight idle intervals separate runs; no sorting, clipping, or cancellation across idle intervals, labels or threads.",
            "timestamp_tolerance_milliseconds": TIME_TOLERANCE_MS}
    return result

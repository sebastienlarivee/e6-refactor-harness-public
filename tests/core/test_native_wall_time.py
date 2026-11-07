"""Offline regression coverage for signed native traces containing idle gaps."""
from __future__ import annotations

import json

import pytest

from lean_tools.native_wall_time import _slices, summarize


def _sample(pairs):
    times, weights, stacks = [], [], []
    for first, last, weight, stack in pairs:
        times.extend([first, last])
        weights.extend([0, weight])
        stacks.extend([stack, stack])
    return {"length": len(times), "time": times, "weight": weights,
            "stack": stacks, "weightType": "tracing-ms"}


def test_signed_trace_preserves_idle_gaps_without_counting_idle_time(tmp_path):
    # Real Lean exports mix zero-weight idle pairs with contained signed tactic
    # slices. The idle interval must contribute no time or connect signed runs.
    sample = _sample([(0, 2, 2, 1), (2, 1, -1, 1), (1, 3, 2, 1),
                      (3, 40, 0, 0),
                      (40, 42, 2, 1), (42, 41, -1, 1), (41, 43, 2, 1)])
    profile = {"meta": {"sampleUnits": {"time": "ms"}}, "threads": [{
        "stackTable": {"frame": [0, 1], "prefix": [None, None]},
        "frameTable": {"func": [0, 1]}, "funcTable": {"name": [0, 1]},
        "stringArray": ["idle", "Elab.step: Lean.Parser.Tactic.exact"],
        "samples": sample}]}
    path = tmp_path / "native-wall-time.json"
    path.write_text(json.dumps(profile))
    original = path.read_bytes()

    result = summarize(path, 8, max_profile_bytes=1_000_000, max_samples=1000)

    assert result["wall_time_milliseconds"] == 6
    assert result["unattributed_milliseconds"] == 0
    assert result["hotspots"][0]["exclusive_slice_milliseconds"] == 6
    assert result["native_slice_accounting"]["raw_negative_samples"] == 2
    assert result["native_slice_accounting"]["threads"][0]["validated_same_label_runs"] == 2
    assert path.read_bytes() == original


@pytest.mark.parametrize("pairs, reason", [
    ([(0, 1, 1, 1), (1, 2, 0, 1), (2, 1.5, -.5, 1), (1.5, 3, 1.5, 1)],
     "invalid zero-weight idle interval"),
    ([(0, 2, 2, 1), (2, 1, 0, 0), (1, .5, -.5, 1), (.5, 3, 2.5, 1)],
     "invalid zero-weight idle interval"),
    ([(0, 2, 2, 1), (2, 1, -1, 1), (1.5, 3, 0, 0)],
     "discontinuous native slice endpoints"),
    ([(0, 2, 2, 1), (2, 1, -1, 2), (1, 3, 2, 2)],
     "a same-label excursion crosses its interval boundary"),
    ([(0, 2, 2, 1), (2, 10, 0, 0), (10, 1, -9, 1), (1, 12, 11, 1)],
     "a same-label excursion crosses its interval boundary"),
    ([(0, 2, 2, 1), (2, 1, -.5, 1), (1, 3, 2, 1)],
     "native weight disagrees with its timestamp difference"),
])
def test_idle_support_preserves_signed_trace_validation(pairs, reason):
    with pytest.raises(ValueError, match=reason):
        _slices(_sample(pairs), [None, "Lean.Parser.Tactic.exact", "Lean.Parser.Tactic.apply"])


def test_idle_pair_requires_the_same_stack():
    sample = _sample([(0, 2, 2, 1), (2, 1, -1, 1), (1, 3, 2, 1), (3, 10, 0, 0)])
    sample["stack"][-1] = 1
    with pytest.raises(ValueError, match="invalid native slice pair"):
        _slices(sample, [None, "Lean.Parser.Tactic.exact"])

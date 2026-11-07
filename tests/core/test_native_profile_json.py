"""Incremental native-profile parsing, budgets, and malformed-input coverage."""
from __future__ import annotations

import json

import pytest

from lean_tools import native_profile_json as reader
from lean_tools.native_wall_time import summarize


def profile(*, weights=None, stacks=None, times=None):
    weights = [0, 2, 0, -1, 0, 2, 0, 0] if weights is None else weights
    stacks = [1] * 6 + [0, 0] if stacks is None else stacks
    times = [0, 2, 2, 1, 1, 3, 3, 40] if times is None else times
    return {'meta': {'sampleUnits': {'time': 'ms'}}, 'threads': [{
        'samples': {'length': len(weights), 'weightType': 'tracing-ms',
                    'weight': weights, 'time': times, 'stack': stacks,
                    'threadCPUDelta': list(weights)},
        'stackTable': {'frame': [0, 1], 'prefix': [None, None]},
        'frameTable': {'func': [0, 1]}, 'funcTable': {'name': [0, 1]},
        'stringArray': ['idle', 'Elab.step: Lean.Parser.Tactic.exact λ"\\']}]}


def run(tmp_path, data, **kwargs):
    path = tmp_path / 'profile.json'
    path.write_text(data if isinstance(data, str) else json.dumps(data, ensure_ascii=False), encoding='utf-8')
    return summarize(path, 8, max_profile_bytes=kwargs.get('max_bytes', 1_000_000),
                     max_samples=kwargs.get('max_samples', 1000))


@pytest.mark.parametrize('chunk', [8, 31, 256, 65536])
def test_column_batches_and_strings_cross_read_boundaries(tmp_path, monkeypatch, chunk):
    # Chunks need not line up with exponent tokens, escaped strings, or columns.
    monkeypatch.setattr(reader, 'CHUNK_CHARS', chunk)
    data = profile()
    result = run(tmp_path, data)
    assert result['complete']
    assert result['samples'] == 8
    assert result['wall_time_milliseconds'] == 3
    assert result['hotspots'][0]['exclusive_slice_milliseconds'] == 3
    assert result['native_slice_accounting']['raw_negative_samples'] == 1


@pytest.mark.parametrize('chunk', [1, 7, 65536])
def test_positive_columns_need_not_have_signed_pair_fields(tmp_path, monkeypatch, chunk):
    monkeypatch.setattr(reader, 'CHUNK_CHARS', chunk)
    data = profile(weights=[0.000001, 2e-6, 3e-6], stacks=[1, 1, 0])
    del data['threads'][0]['samples']['time']
    del data['threads'][0]['samples']['weightType']
    result = run(tmp_path, data)
    assert result['complete']
    assert result['wall_time_milliseconds'] == .000006
    assert result['unattributed_milliseconds'] == .000003


def test_deadline_is_checked_inside_one_large_signed_run():
    from lean_tools.native_wall_time import _iter_signed_runs
    # One same-label run is consumed by fsum before it yields a result. A
    # deadline check must still interrupt it rather than wait for that yield.
    times = [0, 2, 2, 1, 1, 3]
    weights = [0, 2, 0, -1, 0, 2]
    for first in range(3, 20_000):
        times.extend([first, first + 1])
        weights.extend([0, 1])
    sample = {'time': times, 'weight': weights, 'stack': [0] * len(times), 'weightType': 'tracing-ms'}
    checks = 0

    def expired():
        nonlocal checks
        checks += 1
        if checks > 1:
            raise reader.ProfileBudgetExceeded('test parsing deadline')

    with pytest.raises(reader.ProfileBudgetExceeded, match='deadline'):
        next(_iter_signed_runs(sample, ['Lean.Parser.Tactic.exact'], expired))
    assert checks == 2


def test_meta_can_follow_threads_and_all_threads_count_toward_cap(tmp_path):
    original = profile()
    data = {'threads': original['threads'] * 2, 'meta': original['meta']}
    assert run(tmp_path, data)['samples'] == 16
    result = run(tmp_path, data, max_samples=15)
    assert not result['complete'] and result['hotspots'] == []
    assert '15 sample' in result['profile_note']
    data['meta']['sampleUnits']['time'] = 'seconds'
    with pytest.raises(ValueError, match='units'):
        run(tmp_path, data)


def test_exact_integer_timestamps_survive_packed_float_columns(tmp_path):
    base = 2**54
    data = profile(weights=[0, 2, 0, -1, 0, 2], stacks=[1] * 6,
                   times=[base, base + 2, base + 2, base + 1, base + 1, base + 3])
    result = run(tmp_path, data)
    assert result['complete'] and result['wall_time_milliseconds'] == 3


def test_exact_integer_override_storage_is_bounded(tmp_path, monkeypatch):
    monkeypatch.setattr(reader, 'MAX_EXACT_INTEGER_OVERRIDES', 1)
    data = profile(weights=[2**54 + 1, 2**54 + 3], stacks=[1, 1])
    result = run(tmp_path, data)
    assert not result['complete'] and 'exact-integer' in result['profile_note']


@pytest.mark.parametrize('data', [
    '{"meta":{},"meta":{},"threads":[]}',
    '{"threads":[{"samples":{},"samples":{}}]}',
    '{"threads":[{"samples":{"weight":[],"weight":[]}}]}',
    '{"threads":[{"stackTable":{"frame":[],"frame":[]}}]}',
    '{"unknown":{"same":0,"same":1},"threads":[]}',
    '{"threads":[],"meta":{},}',
    '{"threads":[],"unknown":[1,]}',
    '{"threads":[],"unknown":{"x":}}',
    '{"threads":[],"unknown":NaN}',
    '{"threads":[]} garbage',
    '{"threads":[',
    '{"threads":[],"unknown":"unterminated',
])
def test_rejects_malformed_unknown_fields_duplicates_and_truncation(tmp_path, data):
    with pytest.raises(ValueError):
        run(tmp_path, data)


@pytest.mark.parametrize('suffix', [',]', ',,1]', ',true]', ',{}]', ',NaN]', ',Infinity]', ',1e999]'])
def test_rejects_invalid_sample_numeric_batches(tmp_path, monkeypatch, suffix):
    monkeypatch.setattr(reader, 'CHUNK_CHARS', 8)
    data = json.dumps(profile()).replace('"weight": [0, 2, 0, -1, 0, 2, 0, 0]',
        '"weight": [0,2,0,-1,0,2,0,0' + suffix)
    with pytest.raises(ValueError):
        run(tmp_path, data)


@pytest.mark.parametrize('change, message', [
    (lambda data: data['threads'][0]['samples'].update(length=9), 'length mismatch'),
    (lambda data: data['threads'][0]['samples'].update(stack=[1] * 7 + [2]), 'sample stack'),
    (lambda data: data['threads'][0]['stackTable'].update(prefix=[None, 1]), 'stack hierarchy'),
    (lambda data: data['threads'][0]['stackTable'].update(frame=[0, 2]), 'table index'),
    (lambda data: data['threads'][0]['samples'].update(weightType='samples'), 'weight type'),
    (lambda data: data['threads'][0]['samples'].update(time=[0] * 7), 'paired native timestamps'),
    (lambda data: data['threads'][0]['samples'].update(stack=[True] * 8), 'sample stack'),
])
def test_preserves_sample_and_stack_validation(tmp_path, change, message):
    data = profile()
    change(data)
    with pytest.raises(ValueError, match=message):
        run(tmp_path, data)


@pytest.mark.parametrize('bound, value, data', [
    ('MAX_SCALAR_CHARS', 12, '{"unknown":"' + 'x' * 30 + '","threads":[]}'),
    ('MAX_DEPTH', 2, {'unknown': [[[0]]], 'threads': []}),
    ('MAX_OBJECT_KEYS', 1, {'unknown': {'a': 1, 'b': 2}, 'threads': []}),
    ('MAX_KEY_CHARS', 5, {'long_unknown_key': 0, 'threads': []}),
    ('MAX_TABLE_VALUES', 3, profile()),
    ('MAX_TABLE_STRING_CHARS', 5, profile()),
    ('MAX_SCRATCH_BYTES', 8, profile()),
    ('MAX_PARSE_SECONDS', -1, profile()),
])
def test_internal_budgets_return_incomplete_not_partial_success(tmp_path, monkeypatch, bound, value, data):
    monkeypatch.setattr(reader, bound, value)
    result = run(tmp_path, data)
    assert result['complete'] is False
    assert result['truncated'] is True
    assert result['hotspots'] == []
    assert 'bound' in result['profile_note']


def test_size_and_single_column_sample_caps_are_reported_precisely(tmp_path):
    assert '10 byte' in run(tmp_path, profile(), max_bytes=10)['profile_note']
    assert '7 sample' in run(tmp_path, profile(), max_samples=7)['profile_note']


def test_private_scratch_is_closed_after_invalid_summary(tmp_path, monkeypatch):
    opened = []
    original = reader.tempfile.TemporaryFile

    def track(*args, **kwargs):
        file = original(*args, **kwargs)
        opened.append(file)
        return file

    monkeypatch.setattr(reader.tempfile, 'TemporaryFile', track)
    data = profile()
    data['threads'][0]['samples']['stack'][-1] = 2
    with pytest.raises(ValueError):
        run(tmp_path, data)
    assert opened and all(file.closed for file in opened)

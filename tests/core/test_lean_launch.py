from __future__ import annotations
import json
import os
import subprocess
import sys
import time
from contextlib import contextmanager
from pathlib import Path
from types import SimpleNamespace
import pytest
from lean_tools import arena_workflow as arena
from lean_tools import lean_launch as launch

@pytest.fixture
def workspace(tmp_path: Path):
    root = tmp_path / 'project'
    root.mkdir()
    elan = tmp_path / 'elan'
    install = elan / 'toolchains/leanprover--lean4---v4.26.0'
    (install / 'bin').mkdir(parents=True)
    suffix = '.exe' if os.name == 'nt' else ''
    lean = install / 'bin' / ('lean' + suffix)
    lake = install / 'bin' / ('lake' + suffix)
    lean.write_bytes(b'pinned lean executable')
    lake.write_bytes(b'pinned lake executable')
    (install / 'lib/lean').mkdir(parents=True)
    githash = 'a' * 40
    (install / 'lib/lean/Init.olean').write_bytes(b'olean\x02\x01test\x00' + githash.encode() + b'\x00')
    (install / 'include/lean').mkdir(parents=True)
    (install / 'include/lean/version.h').write_text('#define LEAN_PLATFORM_TARGET "test-platform"\n')
    (root / 'lean-toolchain').write_text('leanprover/lean4:v4.26.0\n')
    (root / 'lakefile.toml').write_text('name = "Demo"\n')
    package = root / '.lake/packages/dep'
    (package / '.git').mkdir(parents=True)
    head = 'b' * 40
    (package / '.git/HEAD').write_text(head + '\n')
    config = package / 'lakefile.lean'
    config.write_text('import Lake\nopen Lake DSL\npackage dep\n')
    compiled = package / '.lake/config/dep'
    compiled.mkdir(parents=True)
    (compiled / 'lakefile.olean').write_bytes(b'compiled lakefile')
    trace = compiled / 'lakefile.olean.trace'
    trace.write_text(json.dumps({'name': 'dep', 'options': {}, 'platform': 'test-platform', 'leanHash': githash, 'configHash': launch.lake_text_hash(config.read_text())}))
    manifest = {'name': 'Demo', 'packagesDir': '.lake/packages', 'packages': [{'name': 'dep', 'type': 'git', 'rev': head, 'configFile': 'lakefile.lean'}]}
    (root / 'lake-manifest.json').write_text(json.dumps(manifest))
    environment = {'ELAN_HOME': str(elan), 'PATH': str(tmp_path / 'ambient-bin'), 'SECRET_TOKEN': 'private-token-original', launch.CACHE_ENV: str(tmp_path / 'cache')}
    exported = {key: None for key in launch.ENVIRONMENT_KEYS}
    exported.update(LEAN=str(lean.resolve()), LAKE=str(lake.resolve()), LEAN_SYSROOT=str(install.resolve()), LEAN_GITHASH=githash, PATH=str(install / 'bin') + os.pathsep + environment['PATH'], LEAN_PATH=str(package / '.lake/build/lib/lean'), ELAN_TOOLCHAIN='leanprover/lean4:v4.26.0')
    return SimpleNamespace(root=root, package=package, config=config, trace=trace, install=install, lean=lean, lake=lake, environment=environment, exported=exported, manifest=manifest)

def fake_export(monkeypatch, workspace, *, stderr='', on_communicate=None):
    calls = []

    class Process:
        pid = 123
        returncode = 0

        def __init__(self, command, **kwargs):
            calls.append((command, kwargs))

        def communicate(self, timeout):
            assert timeout > 0
            if on_communicate:
                on_communicate()
            return (json.dumps(workspace.exported), stderr)
    monkeypatch.setattr(launch.subprocess, 'Popen', Process)
    return calls

def prepare(workspace, **kwargs):
    return launch.prepare_launch(workspace.root, deadline=time.perf_counter() + 30, environment=workspace.environment, **kwargs)

def test_cache_exports_whitelist_once_and_keeps_secrets_child_scoped(workspace, monkeypatch):
    calls = fake_export(monkeypatch, workspace, stderr='private-stderr-secret')
    events = []
    original = dict(os.environ)
    first = prepare(workspace, record_event=lambda kind, value: events.append((kind, value)))
    workspace.environment['SECRET_TOKEN'] = 'private-token-new'
    second = prepare(workspace, record_event=lambda kind, value: events.append((kind, value)))
    assert len(calls) == 1
    assert first.provenance['status'] == 'miss'
    assert second.provenance['status'] == 'hit'
    assert first.environment['SECRET_TOKEN'] == 'private-token-original'
    assert second.environment['SECRET_TOKEN'] == 'private-token-new'
    assert first.executable == str(workspace.lean.resolve())
    assert 'SECRET_TOKEN' not in calls[0][0][-1]
    persisted = Path(first.provenance['cache_path']).read_text()
    logged = json.dumps(events)
    for secret in ('private-token-original', 'private-token-new', 'private-stderr-secret'):
        assert secret not in persisted + logged
    assert dict(os.environ) == original


@pytest.mark.parametrize('key', ['LEAN', 'LEAN_GITHASH'])
def test_different_exported_toolchain_identity_is_rejected(workspace, monkeypatch, key):
    workspace.exported[key] = 'wrong-toolchain'
    fake_export(monkeypatch, workspace)
    with pytest.raises(launch.LaunchCacheError):
        prepare(workspace)

def test_changed_dependency_configuration_recaptures_environment(workspace, monkeypatch):
    calls = fake_export(monkeypatch, workspace)
    prepare(workspace)
    workspace.config.write_text(workspace.config.read_text() + '-- new configuration\n')
    trace = json.loads(workspace.trace.read_text())
    trace['configHash'] = launch.lake_text_hash(workspace.config.read_text())
    workspace.trace.write_text(json.dumps(trace))
    prepare(workspace)
    assert len(calls) == 2

@pytest.mark.parametrize('missing', ['compiled', 'executable'])
def test_incomplete_setup_never_builds_or_launches_lake(workspace, monkeypatch, missing):
    paths = {'compiled': workspace.trace.with_suffix(''), 'executable': workspace.lean}
    paths[missing].unlink()
    monkeypatch.setattr(launch.subprocess, 'Popen', lambda *a, **kw: pytest.fail('setup must not launch Lake'))
    with pytest.raises(launch.LaunchCacheError):
        prepare(workspace)

def test_stale_compiled_config_and_git_revision_never_build_or_fetch(workspace, monkeypatch):
    monkeypatch.setattr(launch.subprocess, 'Popen', lambda *a, **kw: pytest.fail('must not build or fetch'))
    workspace.config.write_text(workspace.config.read_text() + '-- stale\n')
    with pytest.raises(launch.LaunchCacheError, match='up-to-date compiled'):
        prepare(workspace)
    (workspace.package / '.git/HEAD').write_text('c' * 40)
    with pytest.raises(launch.LaunchCacheError, match='HEAD differs'):
        prepare(workspace)


def test_indexed_lake_configs_are_checked_at_the_manifest_position(workspace):
    old_install = workspace.install
    new_install = old_install.with_name('leanprover--lean4---v4.30.0')
    old_install.rename(new_install)
    (workspace.root / 'lean-toolchain').write_text('leanprover/lean4:v4.30.0\n')
    indexed = workspace.root / '.lake/config/1'
    indexed.mkdir(parents=True)
    workspace.trace.with_suffix('').replace(indexed / 'lakefile.olean')
    trace = json.loads(workspace.trace.read_text())
    trace['idx'] = 1
    indexed_trace = indexed / 'lakefile.olean.trace'
    indexed_trace.write_text(json.dumps(trace))
    guard = launch.workspace_guard(workspace.root, workspace.environment)
    assert any((item['path'] == str(indexed_trace.resolve()) for item in guard['files']))
    trace['idx'] = 2
    indexed_trace.write_text(json.dumps(trace))
    with pytest.raises(launch.LaunchCacheError, match='up-to-date compiled'):
        launch.workspace_guard(workspace.root, workspace.environment)

def test_exporter_timeout_kills_tree_and_does_not_publish_cache(workspace, monkeypatch):
    killed = []
    budgets = []

    class Process:
        pid = 123
        returncode = None
        stdout = stderr = None

        def communicate(self, timeout):
            budgets.append(timeout)
            if len(budgets) == 1:
                raise subprocess.TimeoutExpired('export', timeout)
            return ('', '')
    monkeypatch.setattr(launch.subprocess, 'Popen', lambda *a, **kw: Process())
    with pytest.raises(launch.LaunchCacheError, match='exporter timed out'):
        prepare(workspace, terminate_process=lambda process: killed.append(process.pid))
    assert killed == [123]
    assert 0 < budgets[0] <= 30
    assert budgets[1] == 5
    assert not list(Path(workspace.environment[launch.CACHE_ENV]).rglob('*.json'))

def test_workspace_change_during_export_is_rejected(workspace, monkeypatch):
    fake_export(monkeypatch, workspace, on_communicate=lambda: workspace.lean.write_bytes(b'changed'))
    with pytest.raises(launch.LaunchCacheError, match='workspace changed'):
        prepare(workspace)
    assert not list(Path(workspace.environment[launch.CACHE_ENV]).rglob('*.json'))

def test_malformed_or_tampered_cache_is_recaptured(workspace, monkeypatch):
    calls = fake_export(monkeypatch, workspace)
    first = prepare(workspace)
    cache = Path(first.provenance['cache_path'])
    payload = json.loads(cache.read_text())
    payload['environment']['SECRET_TOKEN'] = 'private-tampered-value'
    cache.write_text(json.dumps(payload))
    second = prepare(workspace)
    assert len(calls) == 2
    assert second.provenance['status'] == 'stale'
    assert 'private-tampered-value' not in cache.read_text()
    cache.write_text('malformed JSON')
    assert prepare(workspace).provenance['status'] == 'stale'
    assert len(calls) == 3


def test_supplied_lean_paths_follow_lake_workspace_order(tmp_path):
    ambient = {'LEAN_PATH': os.pathsep.join(['ambient-a', 'ambient-b'])}
    child = {'LEAN_PATH': os.pathsep.join(['workspace', 'toolchain', 'ambient-a', 'ambient-b'])}
    launch.add_lean_path_prefixes(child, ambient, [tmp_path])
    assert child['LEAN_PATH'].split(os.pathsep) == ['workspace', 'toolchain', str(tmp_path.resolve()), 'ambient-a', 'ambient-b']
    with pytest.raises(launch.LaunchCacheError, match='ambient suffix'):
        launch.add_lean_path_prefixes({'LEAN_PATH': 'other'}, ambient, [tmp_path])

class Memory:
    peak_bytes = 20

    def __init__(self, pid):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *args):
        pass

    def metadata(self):
        return {}


def test_compile_scope_gives_full_watchdog_after_long_queues_and_export(tmp_path, monkeypatch):
    now = [100.0]
    calls = []
    monkeypatch.setenv('LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE', 'compile')
    monkeypatch.setenv('LEAN_REFACTOR_COLD_LEAN_GATE', str(tmp_path / 'gate'))
    monkeypatch.setenv('LEAN_REFACTOR_COLD_LEAN_CAPACITY', '2')
    monkeypatch.setenv(launch.CACHE_ENV, str(tmp_path / 'cache'))

    @contextmanager
    def permit(resource, **kwargs):
        calls.append((resource, kwargs['timeout_seconds']))
        now[0] += 20
        yield SimpleNamespace(queued_at='queued', admitted_at='admitted', queue_wait_seconds=20)

    def prepared(root, **kwargs):
        assert kwargs['deadline'] is None and kwargs['export_timeout_seconds'] == 10
        now[0] += 8
        return launch.LaunchEnvironment('pinned-lean', {}, {'status': 'hit'})

    class Process:
        pid, returncode = (123, 0)

        def communicate(self, *, timeout):
            calls.append(('compile', timeout))
            now[0] += 1
            return ('done', None)
    monkeypatch.setattr(arena.time, 'perf_counter', lambda: now[0])
    monkeypatch.setattr(arena.resource_gate, 'permit_from_environment', permit)
    monkeypatch.setattr(launch, 'prepare_launch', prepared)
    monkeypatch.setattr(arena.subprocess, 'Popen', lambda *a, **kw: Process())
    monkeypatch.setattr(arena, 'ProcessTreeMemoryMonitor', Memory)
    monkeypatch.setattr(arena, 'process_peak_working_set_bytes', lambda *_: None)
    monkeypatch.setattr(arena, 'artifact_root_path', lambda: None)
    events = []
    monkeypatch.setattr(arena, 'record_event', lambda kind, payload: events.append(payload))
    result = arena.run_lean(tmp_path / 'Demo.lean', tmp_path, 10)
    assert calls == [('cold_lean', None), ('lean', None), ('compile', 10)]
    assert result.queue_wait_seconds == 40 and result.seconds == 9
    assert events[-1]['timeout_scope'] == 'compile' and events[-1]['total_wall_seconds'] == 49

def test_export_watchdog_does_not_include_cache_lock_wait(workspace, monkeypatch):
    now, calls = ([0.0], [])

    @contextmanager
    def acquire(self, **kwargs):
        assert kwargs['timeout_seconds'] is None
        now[0] += 100
        yield None
    monkeypatch.setattr(launch.time, 'perf_counter', lambda: now[0])
    monkeypatch.setattr(launch.resource_gate.FilePermitPool, 'acquire', acquire)

    class Process:
        pid, returncode = (123, 0)

        def communicate(self, *, timeout):
            calls.append(timeout)
            return (json.dumps(workspace.exported), '')
    monkeypatch.setattr(launch.subprocess, 'Popen', lambda *a, **kw: Process())
    launch.prepare_launch(workspace.root, deadline=None, export_timeout_seconds=10, environment=workspace.environment)
    assert calls == [10]


@pytest.mark.parametrize('inherited_nice', [0, 10])
def test_native_child_priority_is_background_and_does_not_compound(inherited_nice):
    code = (
        'import os,subprocess,sys; from lean_tools import lean_launch; '
        'os.nice(' + str(inherited_nice) + '); '
        'probe=[sys.executable,"-c","import os; print(os.getpriority(os.PRIO_PROCESS, 0))"]; '
        'print(subprocess.check_output(lean_launch.native_command(probe),text=True).strip())'
    )
    observed = subprocess.check_output([sys.executable, '-c', code], text=True)
    assert int(observed.strip()) == 10

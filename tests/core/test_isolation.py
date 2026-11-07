"""Harmless isolation checks for file privacy and shared admission behavior."""
import json
import os
import subprocess
from pathlib import Path

import pytest

from e6 import config, isolation
from e6.experiment import DEFAULT_RUN_SPEC
from lean_tools import resource_gate
from lean_tools import arena_workflow as arena


def test_isolation_blocks_host_files_and_preserves_occupied_lean_gate(tmp_path):
    capsule = tmp_path / 'capsule'
    capsule.mkdir()
    gate = tmp_path / 'lean-gate'
    forbidden = tmp_path / 'archived-sentinel'
    forbidden.write_text('SYNTHETIC_ARCHIVE')
    parent_pid = os.getpid()
    pool = resource_gate.FilePermitPool(gate, 'review', 1)
    with pool.acquire(timeout_seconds=1), forbidden.open() as descriptor:
        hidden = [str(forbidden), f'/proc/{parent_pid}/root{forbidden}',
                  f'/proc/{parent_pid}/fd/{descriptor.fileno()}', f'/proc/{parent_pid}/environ']
        code = 'import json,os; from pathlib import Path; from lean_tools import resource_gate; hidden=' + repr(hidden) + '; result={}\n'
        code += 'for p in hidden:\n try:\n  open(p).read(); result[p]=True\n except OSError: result[p]=False\n'
        code += 'try:\n with resource_gate.FilePermitPool(Path(' + repr(str(gate)) + '), "review", 1).acquire(timeout_seconds=.03): result["occupied_gate_admitted"]=True\nexcept resource_gate.ResourceGateError:\n result["occupied_gate_admitted"]=False\n'
        code += ('open("allowed", "w").write("allowed"); '
                 'result["host_key_absent"]="OPENAI_API_KEY" not in os.environ; '
                 'print(json.dumps(result))')
        settings = {**DEFAULT_RUN_SPEC.proof_settings(), 'codex': str(config.find_codex()), 'model_catalog': str(config.MODEL_CATALOG)}
        command, environment = isolation.wrap_command(settings, capsule,
            ['/usr/bin/python3', '-c', code], [capsule, gate], {'OPENAI_API_KEY': 'synthetic-key'})
        result = subprocess.run(command, cwd=capsule, env=environment, text=True, capture_output=True, timeout=5)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert all(report[path] is False for path in hidden)
    assert report['occupied_gate_admitted'] is False and report['host_key_absent']
    assert (capsule / 'allowed').read_text() == 'allowed'


def test_original_visible_feedback_keeps_project_readonly_and_each_pass_history_private(tmp_path):
    from dataclasses import replace
    from e6.experiment import DEFAULT_RUN_SPEC
    project = tmp_path / 'project'
    project.mkdir()
    source = project / 'Target.lean'
    source.write_text('ORIGINAL_PROOF\nORIGINAL_SOURCE_SUFFIX\n')
    archive = tmp_path / 'previous-panel-solution.lean'
    archive.write_text('SYNTHETIC_ARCHIVE')
    settings = {**replace(DEFAULT_RUN_SPEC, first_pass_reprove=False).proof_settings(),
                'codex': str(config.find_codex()), 'primary': str(project), 'compatibility': []}
    previous = None
    for number in (1, 2):
        capsule = tmp_path / 'run' / f'pass-{number:03d}'
        capsule.mkdir(parents=True)
        hidden = [archive, *([previous / 'prior-notes.txt'] if previous else [])]
        code = ('import json,os; from pathlib import Path; source=Path(' + repr(str(source)) + '); '
                'marker=Path(os.environ["CODEX_HOME"])/"synthetic-session.json"; '
                'result={"source":source.read_text(), "fresh_home":not marker.exists()}\n'
                'try:\n source.write_text("changed"); result["readonly"]=False\n'
                'except OSError:\n result["readonly"]=True\n'
                'for p in ' + repr([str(path) for path in hidden]) + ':\n'
                ' try:\n  Path(p).read_text(); result[p]=True\n'
                ' except OSError:\n  result[p]=False\n'
                'marker.write_text("SYNTHETIC_SESSION"); print(json.dumps(result))')
        command, environment = isolation.wrap_command(settings, capsule,
            ['/usr/bin/python3', '-c', code], [capsule], {'CODEX_HOME': str(tmp_path / 'old-home')})
        result = subprocess.run(command, cwd=capsule, env=environment, text=True,
                                capture_output=True, timeout=5)
        assert result.returncode == 0, result.stderr
        observed = json.loads(result.stdout)
        assert observed['source'] == source.read_text()
        assert observed['readonly'] and observed['fresh_home']
        assert all(observed[str(path)] is False for path in hidden)
        report = json.loads((capsule / 'isolation.json').read_text())
        assert not report['statement_first']
        assert report['masked_source_files'] == report['masked_compiled_or_history_files'] == []
        assert report['masked_history_directories'] == []
        (capsule / 'prior-notes.txt').write_text('SYNTHETIC_PREVIOUS_PASS')
        previous = capsule


def test_isolation_refuses_a_broad_host_mount(tmp_path):
    capsule = tmp_path / 'capsule'
    capsule.mkdir()
    settings = {**DEFAULT_RUN_SPEC.proof_settings(), 'codex': str(config.find_codex())}
    with pytest.raises(ValueError, match='broad filesystem mount'):
        isolation.wrap_command(settings, capsule, ['/usr/bin/true'], [Path.home()], {})


def test_isolation_exposes_only_the_readonly_provisioned_helper(tmp_path):
    root = tmp_path / 'cell'
    capsule = root / 'pass-001'
    capsule.mkdir(parents=True)
    cache = root / 'warm-broker/private-evaluation-cache'
    key = 'a' * 64
    helper = cache / 'helpers' / key[:2] / key
    helper.mkdir(parents=True)
    for name in ('LrhMeasurement.lean', 'LrhMeasurement.olean', 'ready.json'):
        (helper / name).write_text('SYNTHETIC_GENERATED_HELPER')
    hidden = [cache / 'prior-candidate.json', root / 'warm-broker/ManagedQuick.lean']
    for path in hidden:
        path.write_text('SYNTHETIC_PRIVATE_HOST_ARTIFACT')
    code = ('import json; from pathlib import Path; result={}; '
            'helper=Path(' + repr(str(helper / 'LrhMeasurement.lean')) + '); '
            'result["helper"]=helper.read_text()\n'
            'try:\n helper.write_text("changed"); result["readonly"]=False\n'
            'except OSError:\n result["readonly"]=True\n'
            'for p in ' + repr([str(path) for path in hidden]) + ':\n'
            ' try:\n  Path(p).read_text(); result[p]=True\n'
            ' except OSError:\n  result[p]=False\n'
            'print(json.dumps(result))')
    settings = {**DEFAULT_RUN_SPEC.proof_settings(), 'root': str(root), 'codex': str(config.find_codex())}
    command, environment = isolation.wrap_command(settings, capsule,
        ['/usr/bin/python3', '-c', code], [capsule],
        {'LEAN_REFACTOR_FEEDBACK_SUPPORT': json.dumps([str(helper)])})
    result = subprocess.run(command, cwd=capsule, env=environment, text=True, capture_output=True, timeout=5)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['helper'] == 'SYNTHETIC_GENERATED_HELPER' and report['readonly']
    assert all(report[str(path)] is False for path in hidden)


def test_retrieval_index_mount_is_readonly_and_exposes_no_cache_siblings(tmp_path):
    capsule = tmp_path / 'capsule'
    capsule.mkdir()
    cache = tmp_path / 'host-index-cache'
    cache.mkdir()
    index = cache / 'original-prefix.sqlite3'
    index.write_text('SYNTHETIC_PREFIX_INDEX')
    hidden = cache / 'other-pass-notes'
    hidden.write_text('SYNTHETIC_PRIVATE_DATA')
    settings = {**DEFAULT_RUN_SPEC.proof_settings(), 'codex': str(config.find_codex()),
                'retrieval_index': {'path': str(index), 'sha256': arena.sha256_file(index)}}
    code = ('import json; from pathlib import Path; '
            'index=Path(' + repr(str(index)) + '); result={"index":index.read_text()}\n'
            'try:\n index.write_text("changed"); result["readonly"]=False\n'
            'except OSError:\n result["readonly"]=True\n'
            'try:\n Path(' + repr(str(hidden)) + ').read_text(); result["sibling_visible"]=True\n'
            'except OSError:\n result["sibling_visible"]=False\n'
            'print(json.dumps(result))')
    command, environment = isolation.wrap_command(settings, capsule,
        ['/usr/bin/python3', '-c', code], [capsule], {})
    result = subprocess.run(command, cwd=capsule, env=environment, text=True, capture_output=True, timeout=5)
    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout) == {'index': 'SYNTHETIC_PREFIX_INDEX', 'readonly': True,
                                       'sibling_visible': False}
    assert index.read_text() == 'SYNTHETIC_PREFIX_INDEX'


@pytest.mark.parametrize('mutable', [False, True])
def test_isolation_refuses_changed_or_agent_writable_retrieval_index(tmp_path, mutable):
    capsule = tmp_path / 'capsule'
    capsule.mkdir()
    index = (capsule if mutable else tmp_path) / 'original-prefix.sqlite3'
    index.write_text('SYNTHETIC_PREFIX_INDEX')
    settings = {**DEFAULT_RUN_SPEC.proof_settings(), 'codex': str(config.find_codex()), 'retrieval_index': {
        'path': str(index), 'sha256': arena.sha256_file(index) if mutable else '0' * 64}}
    with pytest.raises(ValueError, match='changed or is writable'):
        isolation.wrap_command(settings, capsule, ['/usr/bin/true'], [capsule], {})


def example_artifact(tmp_path):
    from lean_tools import proof_example_search as examples
    project = tmp_path / "source-project"
    project.mkdir()
    (project / "Demo.lean").write_text("prelude\ntheorem analogy : True := by trivial\n")
    row = {"name": "target", "signature": "theorem target : True",
           "src": "theorem target : True := by trivial", "header": "prelude\nimport Demo\n", "contexts": []}
    return examples.prepare_index(row, project, tmp_path / "source-index-cache",
                                  environment_fingerprint="fixed-env", source_roots=[project])






def test_disabled_search_extensions_never_mount_an_ambient_source_index(tmp_path):
    artifact = example_artifact(tmp_path)
    capsule = tmp_path / "capsule"
    capsule.mkdir()
    settings = {**DEFAULT_RUN_SPEC.proof_settings(), "codex": str(config.find_codex()), "examples_index": artifact}
    isolation.wrap_command(settings, capsule, ['/usr/bin/true'], [capsule], {})
    assert artifact["path"] not in json.loads((capsule / "isolation.json").read_text())["readonly"]

from __future__ import annotations
import io
import json
from contextlib import contextmanager
from dataclasses import replace
from pathlib import Path
import pytest
import tomllib
from lean_tools import feedback_workflow as feedback
arena = feedback.arena

@pytest.mark.parametrize('enabled,index,digest', [
    (False, 'index.sqlite3', 'a' * 64),
    (True, 'index.sqlite3', None),
    (True, None, 'a' * 64),
    (True, 'index.sqlite3', 'invalid'),
])
def test_capsule_rejects_incomplete_host_retrieval_index_settings(tmp_path, enabled, index, digest):
    with pytest.raises(ValueError):
        feedback.configure_capsule(tmp_path, tmp_path, goal_retrieval=enabled,
                                   retrieval_index=Path(index) if index else None,
                                   retrieval_index_sha256=digest)

@pytest.fixture
def service(tmp_path):
    row = {'name': 'demo', 'header': 'import Mathlib\n\n', 'contexts': [], 'signature': 'theorem demo : True', 'src': 'theorem demo : True := by trivial', 'proof_length': 2}
    (tmp_path / 'Task.json').write_text(json.dumps({'schema_version': 1, 'row': row}), encoding='utf-8')
    candidate = tmp_path / 'Candidate.lean'
    candidate.write_text(arena.render_candidate_scaffold(row), encoding='utf-8')
    return feedback.Feedback({'task': str(tmp_path / 'Task.json'), 'candidate': str(candidate), 'project_root': str(tmp_path)})

def evaluation(path):
    return arena.Evaluation(task_id='demo', candidate_path=str(path), valid=True, compile_seconds=0.2, axiom_audit_seconds=None, axioms=None, original_local_tokens=2, candidate_local_tokens=3, local_token_reduction_pct=-50, official_original_tokens=2, published_reference_heartbeat=None, local_reference_heartbeat=None, environment_fingerprint='test', heartbeat=None, heartbeat_reduction_pct=None)

def test_rejects_contract_changes_without_writing(service):
    old = service.candidate.read_text(encoding='utf-8')
    for request in ({'source': old.replace('True', 'False')}, {'body': 'by sorry'}, {'edits': [{'old': 'absent', 'new': 'x'}]}, {'body': 'by trivial', 'source': old}, {'expected_sha256': 'stale', 'body': 'by trivial'}):
        with pytest.raises(arena.WorkflowError):
            service.check(request)
        assert service.candidate.read_text(encoding='utf-8') == old

def test_quick_edit_lock_uses_request_allowance_even_with_compile_scope(service, monkeypatch):
    monkeypatch.setenv('LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE', 'compile')
    original_lock = arena.exclusive_file_lock
    waits = []

    @contextmanager
    def lock(path, timeout_seconds, **kwargs):
        waits.append(arena.check_budget.remaining(timeout_seconds))
        with original_lock(path, timeout_seconds, **kwargs):
            yield
    monkeypatch.setattr(arena, 'exclusive_file_lock', lock)
    monkeypatch.setattr(arena, 'evaluate_candidate', lambda _task, source, _project, **_kwargs: evaluation(source))
    result = service.check({})
    assert result['valid'] and len(waits) == 1 and 0 < waits[0] <= service.quick_timeout
    assert result['timeout_scope'] == 'quick_request'

@pytest.mark.parametrize('name', ['../Other.lean', 'sub/Other.lean', 'Task.json', 'C:/Other.lean'])
def test_candidate_is_confined(service, name):
    with pytest.raises(arena.WorkflowError):
        service.check({'candidate': name})

def test_checkpoint_uses_evaluated_snapshot_when_draft_changes(service, monkeypatch):
    observed = []

    def evaluate(task, snapshot, project, **kwargs):
        observed.append(snapshot.read_text(encoding='utf-8'))
        service.candidate.write_text('another simultaneous draft', encoding='utf-8')
        return evaluation(snapshot)
    monkeypatch.setattr(arena, 'evaluate_candidate', evaluate)
    result = service.check({'body': 'by exact True.intro'})
    assert result['status'] == 'valid'
    assert Path(result['checkpoint']).read_text(encoding='utf-8') == observed[0]
    assert arena.sha256_file(Path(result['checkpoint'])) == result['source_sha256']
    assert service.candidate.read_text(encoding='utf-8') == 'another simultaneous draft'
    assert Path(result['details_path']).is_file()


def test_checkpoint_rejects_snapshot_changed_during_evaluation(service, monkeypatch):
    def evaluate(_task, snapshot, _project, **_kwargs):
        snapshot.write_text('changed during evaluation', encoding='utf-8')
        return evaluation(snapshot)
    monkeypatch.setattr(arena, 'evaluate_candidate', evaluate)
    result = service.check({'body': 'by exact True.intro'})
    assert result['status'] == 'check_failed' and result['valid'] is None
    assert 'evaluated snapshot changed' in result['error']
    assert not (service.root / 'valid-candidates').exists()
    assert 'True.intro' in service.candidate.read_text(encoding='utf-8')

@pytest.mark.parametrize('timed_out,status', [(False, 'invalid'), (True, 'timeout')])
def test_failed_check_preserves_draft_but_never_checkpoints(service, monkeypatch, timed_out, status):

    def fail(*args, **kwargs):
        arena.require_lean_success(arena.LeanRun(command=[], returncode=1, seconds=2, output='type mismatch', timed_out=timed_out), 'test')
    monkeypatch.setattr(arena, 'evaluate_candidate', fail)
    result = service.check({'body': 'by exact Nat.zero_le 1'})
    assert result['status'] == status
    assert result['valid'] is (None if timed_out else False)
    assert 'Nat.zero_le' in service.candidate.read_text(encoding='utf-8')
    assert not (service.root / 'valid-candidates').exists()

@pytest.mark.parametrize('same_goal_diagnostics', [False, True])
def test_invalid_summary_deduplicates_diagnostics_and_preserves_full_details(service, monkeypatch, same_goal_diagnostics):
    tools_root = Path(feedback.__file__).resolve().parents[1] / 'tools'
    monkeypatch.syspath_prepend(str(tools_root))
    from lean_tools import lean_goal_state
    diagnostics = [{'severity': 'error', 'message': 'synthetic type mismatch', 'location': {'scope': 'candidate', 'line': 4, 'column': 3}}, {'severity': 'warning', 'message': 'synthetic warning'}]
    goal_diagnostics = diagnostics if same_goal_diagnostics else [{'severity': 'error', 'message': 'different goal diagnostic'}]
    compiler_output = 'candidate:4:3: error: synthetic type mismatch\nsynthetic warning'

    def fail(*_args, **_kwargs):
        arena.require_lean_success(arena.LeanRun(command=['persistent-lean-lsp'], returncode=1, seconds=0.2, output=compiler_output, log_path=str(service.root / 'raw-diagnostics.json')), 'demo: candidate compile')

    def present(_path, _source, result, full):
        result['diagnostics'] = diagnostics
        full['diagnostic_presentation'] = {'diagnostics': diagnostics}
    monkeypatch.setattr(arena, 'evaluate_candidate', fail)
    monkeypatch.setattr(service, 'present_artifact', present)
    monkeypatch.setattr(lean_goal_state, 'query_goal_state', lambda *_args, **_kwargs: {'rendered': '⊢ True', 'position': {'candidate': {'line': 4, 'column': 3}}, 'diagnostics': goal_diagnostics, 'details_path': 'full-goals.json'})
    result = service.check({'goal': {'line': 4}})
    assert result['status'] == 'invalid' and result['valid'] is False
    assert result['error'] == 'demo: candidate compile failed with exit 1'
    assert result['diagnostics'] == diagnostics
    assert result['goals'] == '⊢ True'
    if same_goal_diagnostics:
        assert 'goal_diagnostics' not in result
        assert result['goal_diagnostics_ref'] == 'diagnostics'
    else:
        assert result['goal_diagnostics'] == goal_diagnostics
        assert 'goal_diagnostics_ref' not in result
    full = json.loads(Path(result['details_path']).read_text(encoding='utf-8'))
    assert compiler_output in full['error']
    assert full['lean_run']['output'] == compiler_output
    assert full['goals']['diagnostics'] == goal_diagnostics
    assert full['diagnostic_presentation']['diagnostics'] == diagnostics

def test_failure_without_structured_diagnostics_keeps_compiler_detail(service, monkeypatch):
    compiler_output = 'error: synthetic mismatch\nadditional context'

    def fail(*_args, **_kwargs):
        arena.require_lean_success(arena.LeanRun(command=[], returncode=1, seconds=0.2, output=compiler_output), 'demo: candidate compile')
    monkeypatch.setattr(arena, 'evaluate_candidate', fail)
    result = service.check({})
    assert compiler_output in result['error']
    assert 'goal_diagnostics_ref' not in result

def test_advisory_is_separate_from_exact_validation(service, monkeypatch):
    from lean_tools import advisory_feedback
    monkeypatch.setattr(arena, 'measurement_environment_fingerprint', lambda *a, **k: 'test')
    monkeypatch.setattr(arena, 'evaluate_candidate', lambda *a, **k: pytest.fail('exact cache touched'))
    monkeypatch.setattr(advisory_feedback, 'observe', lambda *a, **k: {'status': 'completed', 'authoritative': False, 'source_sha256': 'instrumented', 'valid': True, 'heartbeat': 17})
    result = service.check({'mode': 'advisory'})
    assert result['heartbeat'] == 17 and result['authoritative'] is False
    assert result['measurement_source_sha256'] == 'instrumented'
    assert result['source_sha256'] == arena.sha256_file(service.candidate)
    assert result['checkpoint'] is None

def test_quick_returns_existing_exact_count_without_remeasuring(service, monkeypatch):
    cache = service.root / 'cache'
    monkeypatch.setenv('LEAN_REFACTOR_EVALUATION_CACHE', str(cache))
    monkeypatch.setattr(arena, 'evaluate_candidate', lambda task, path, project, **k: evaluation(path))
    source = service.candidate.read_text(encoding='utf-8')
    declaration, _ = arena.extract_candidate_declaration(service.row, source)
    key = arena.evaluation_cache_key(service.task, service.row, declaration, 'test', 'exact')
    exact = replace(evaluation(service.candidate), heartbeat=23, axiom_audit_seconds=0.2, axioms=[])
    arena.store_cached_evaluation(arena.evaluation_cache_path(cache, 'exact', key), key, 'exact', 'test', arena.sha256_bytes(declaration.encode()), exact)
    result = service.check({})
    assert result['heartbeat'] == 23 and result['heartbeat_status'] == 'cached_exact'
    changed = service.check({'body': 'by exact True.intro'})
    assert changed['heartbeat'] is None and changed['heartbeat_status'] == 'not_run'

def test_cached_diagnostics_remap_to_current_candidate_markers(service, monkeypatch):
    from lean_tools import diagnostic_presentation as presentation
    current = service.candidate.read_text(encoding='utf-8')
    declaration, _ = arena.extract_candidate_declaration(service.row, current)
    generated = arena.quick_compile_harness(service.row, declaration, service.project)
    old_candidate = arena.render_environment(service.row) + declaration + '\n'
    line = generated.count('\n', 0, generated.index(declaration))
    raw = [{'severity': 'warning', 'line': line, 'character': 0, 'message': 'same warning'} for _ in range(12)]
    old_map = presentation.SourceMap.for_declaration(old_candidate, generated, declaration)
    path = presentation.archive_diagnostics(raw, presentation.present_diagnostics(raw, old_map), source=generated, source_map=old_map, candidate_path=service.root / 'old-snapshot.lean')
    monkeypatch.setattr(arena, 'evaluate_candidate', lambda task, snapshot, project, **kwargs: replace(evaluation(snapshot), diagnostics_path=str(path)))
    result = service.check({})
    assert result['status'] == 'valid'
    assert result['candidate'] == str(service.candidate)
    assert result['diagnostics'][0]['count'] == 12
    assert result['diagnostics'][0]['location'] == {'scope': 'candidate', 'line': line + 2, 'column': 1}
    assert result['diagnostics_path'] == str(path)
    full = json.loads(Path(result['details_path']).read_text(encoding='utf-8'))
    assert len(full['diagnostic_presentation']['mapped_diagnostics']) == 12
    assert json.loads(path.read_text(encoding='utf-8'))['raw_diagnostics'] == raw

def test_missing_diagnostic_artifact_does_not_change_validation(service, monkeypatch):
    monkeypatch.setattr(arena, 'evaluate_candidate', lambda task, snapshot, project, **kwargs: replace(evaluation(snapshot), diagnostics_path=str(service.root / 'missing.json')))
    result = service.check({})
    assert result['status'] == 'valid' and result['valid'] is True
    assert 'artifact unavailable' in result['diagnostics_note']

def test_mcp_roundtrip_handles_error_then_next_request(service, monkeypatch):

    def evaluate(*args, **kwargs):
        print('library noise')
        return evaluation(args[1])
    monkeypatch.setattr(arena, 'evaluate_candidate', evaluate)
    requests = [{'id': 1, 'method': 'initialize'}, {'method': 'notifications/initialized'}, {'id': 2, 'method': 'tools/list'}, {'id': 3, 'method': 'tools/call', 'params': {'name': 'edit_check', 'arguments': []}}, {'id': 4, 'method': 'tools/call', 'params': {'name': 'edit_check', 'arguments': {}}}]
    output = io.StringIO()
    feedback.serve(service, io.StringIO('\n'.join((json.dumps(x) for x in requests)) + '\n'), output)
    replies = [json.loads(line) for line in output.getvalue().splitlines()]
    assert [r['id'] for r in replies] == [1, 2, 3, 4]
    assert replies[1]['result']['tools'][0]['name'] == 'edit_check'
    assert replies[2]['result']['isError'] is True
    assert json.loads(replies[3]['result']['content'][0]['text'])['valid'] is True
    assert 'library noise' not in output.getvalue()

def test_mcp_config_forwards_harness_names_without_token_values(tmp_path, monkeypatch):
    monkeypatch.setenv('LEAN_REFACTOR_PERSISTENT_QUICK_TOKEN', 'private-token')
    feedback.configure_capsule(tmp_path, tmp_path)
    args = feedback.codex_config_args(tmp_path)
    assert 'private-token' not in ' '.join(args)
    config = tomllib.loads('\n'.join(args[1::2]))['mcp_servers']['lean_feedback']
    assert 'LEAN_REFACTOR_PERSISTENT_QUICK_TOKEN' in config['env_vars']


def test_tool_contract_is_shared_by_listing_launcher_and_preflight(service):
    from lean_tools import codex_preflight
    from lean_tools import feedback_contract
    feedback.configure_capsule(service.root, service.project)
    args = feedback.codex_config_args(service.root)
    config = tomllib.loads('\n'.join(args[1::2]))['mcp_servers']['lean_feedback']
    assert config['enabled_tools'] == feedback_contract.enabled_tools()
    assert config['tools'][feedback_contract.TOOL_NAME]['approval_mode'] == 'approve'
    output = io.StringIO()
    feedback.serve(service, io.StringIO('{"id":1,"method":"initialize"}\n{"id":2,"method":"tools/list"}\n'), output)
    verified = codex_preflight._validate_stdio(output.getvalue())
    assert verified['tools'] == feedback_contract.enabled_tools()
    assert verified['tool_invocations'] == 0
    replies = [json.loads(line) for line in output.getvalue().splitlines()]
    replies[1]['result']['tools'].append({'name': 'extra_tool'})
    with pytest.raises(codex_preflight.PreflightError, match='exactly edit_check'):
        codex_preflight._validate_stdio('\n'.join(json.dumps(reply) for reply in replies))


@pytest.mark.parametrize("header,source_form", [("import Lean\n", "ordinary"), ("module\nimport Lean\n", "module")])
def test_profiler_capsule_preflight_and_catalog_are_source_aware(service, header, source_form):
    from lean_tools.feedback_contract import tool_catalog
    from lean_tools.regional_profiler import TOOL
    row = {**service.row, "header": header}
    service.task.write_text(json.dumps({"schema_version": 1, "row": row}))
    path = feedback.configure_capsule(service.root, service.project, regional_profiler=True)
    settings = json.loads(path.read_text())
    capability = settings["profiler_capability"]
    assert capability["available"] is True
    assert capability["source_form"] == source_form
    assert capability["default_timeout_seconds"] == capability["max_timeout_seconds"] == 30
    original = TOOL["description"]
    listed = next(item for item in tool_catalog(settings) if item["name"] == "profile_proof")
    assert f"Capsule source form: {source_form}" in listed["description"]
    assert "Default/maximum timeout per Lean process: 30/30" in listed["description"]
    assert "Validation and profiling have separate process allowances" in listed["description"]
    assert "10-second budget" in listed["description"]
    assert TOOL["description"] == original
    capability.update(available=False, outcome="prefix_unavailable")
    listed = next(item for item in tool_catalog(settings) if item["name"] == "profile_proof")
    assert "Unavailable for this capsule" in listed["description"]
    assert "instead of retrying" in listed["description"]


def test_cli_archive_failure_keeps_exception_output_bounded(service, monkeypatch, capsys):
    from lean_tools import feedback_response
    config = service.root / "cli-config.json"
    config.write_text("{}")
    outside = service.root / "outside"
    outside.mkdir()
    directory = service.root / ".feedback"
    directory.mkdir()
    (directory / "responses").symlink_to(outside, target_is_directory=True)

    def fail(_request):
        raise RuntimeError("synthetic failure \"\n" * 100_000)

    monkeypatch.setattr(service, "check", fail)
    monkeypatch.setattr(feedback, "Feedback", lambda _settings: service)
    monkeypatch.setattr(feedback.sys, "argv", ["feedback_workflow.py", "--config", str(config)])
    monkeypatch.setattr(feedback.sys, "stdin", io.StringIO("{}"))
    assert feedback.main() == 1
    captured = capsys.readouterr()
    result = json.loads(captured.out)
    assert result["status"] == "infrastructure_error" and result["error_details_unavailable"] is True
    assert len(captured.out.encode("utf-8")) < feedback_response.RESPONSE_BYTE_LIMIT
    assert not captured.err and not list(outside.iterdir())

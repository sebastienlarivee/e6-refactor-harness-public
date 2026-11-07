from __future__ import annotations
from contextlib import contextmanager
from pathlib import Path
import pytest
from lean_tools import lean_goal_state as goal_state


def test_map_candidate_cursor_into_managed_prefix() -> None:
    declaration = 'theorem demo (h : True) : True := by\n  exact h'
    candidate_prefix = 'import Mathlib\n\n-- BEGIN\n'
    managed_prefix = 'import Mathlib\n\ndef earlier : True := True.intro\n\n'
    document = goal_state.PreparedDocument(task_name='demo', candidate_path=Path('Candidate.lean'), project_root=Path('.'), source=managed_prefix + declaration + '\n', document_kind='project_source_prefix', candidate_text=candidate_prefix + declaration + '\n-- END\n', candidate_declaration_start=len(candidate_prefix), declaration=declaration, document_declaration_start=len(managed_prefix))
    candidate_line = 5
    candidate, lsp = goal_state.map_candidate_position(document, candidate_line, None)
    assert candidate == {'line': 5, 'column': 3}
    assert lsp == {'line': 5, 'character': 2}

def test_relevant_diagnostics_suppresses_prefix_information_noise() -> None:
    declaration = 'theorem demo : True := by\n  trivial'
    candidate_prefix = '-- BEGIN\n'
    managed_prefix = 'theorem earlier : True := by\n  trivial\n\n'
    document = goal_state.PreparedDocument(task_name='demo', candidate_path=Path('Candidate.lean'), project_root=Path('.'), source=managed_prefix + declaration + '\n', document_kind='project_source_prefix', candidate_text=candidate_prefix + declaration + '\n-- END\n', candidate_declaration_start=len(candidate_prefix), declaration=declaration, document_declaration_start=len(managed_prefix))
    diagnostics = [goal_state.persistent.Diagnostic('information', 0, 0, 'Goals accomplished!'), goal_state.persistent.Diagnostic('information', 3, 0, 'Try this: exact True.intro'), goal_state.persistent.Diagnostic('warning', 0, 0, 'prefix warning'), goal_state.persistent.Diagnostic('error', None, None, 'global failure'), goal_state.persistent.Diagnostic('information', 3, 0, 'Goals accomplished!')]
    relevant, omitted = goal_state.relevant_diagnostics(diagnostics, document)
    assert omitted == 2
    assert [item['message'] for item in relevant] == ['global failure', 'Try this: exact True.intro', 'prefix warning']
    assert relevant[1]['location']['scope'] == 'candidate'

def test_goal_query_uses_resident_source_version(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    source = 'theorem demo : True := by\n  trivial'
    document = goal_state.PreparedDocument(task_name='demo', candidate_path=tmp_path / 'Candidate.lean', project_root=tmp_path, source=source, document_kind='supplied_environment', candidate_text=source, candidate_declaration_start=0, declaration=source, document_declaration_start=0)
    monkeypatch.setattr(goal_state, 'prepare_document', lambda *_args: document)
    monkeypatch.setattr(goal_state.arena, 'persistent_quick_matches_project', lambda _root: True)
    monkeypatch.setattr(goal_state, 'GoalStateSession', lambda *_args: pytest.fail('cold goal session started'))

    def request(received, timeout, **kwargs):
        assert received == source and 0 < timeout <= 5
        assert kwargs == {'operation': 'goals', 'position': {'line': 1, 'character': 2}, 'target_start_line': 0}
        return {'goals': {'goals': [{'type': {'text': 'True'}, 'hyps': []}]}, 'diagnostics': [], 'startup_seconds': 0, 'elaboration_seconds': 0, 'document_version': 4, 'reused_source': True, 'diagnostics_omitted': 12}
    monkeypatch.setattr(goal_state.persistent, 'feedback_request', request)
    result = goal_state.query_goal_state(tmp_path / 'task.json', document.candidate_path, tmp_path, line=2, column=None, timeout_seconds=5)
    assert result['backend'] == 'resident' and result['document_version'] == 4
    assert result['reused_source'] is True and result['diagnostics_omitted'] == 12
    assert result['rendered'] == '⊢ True'

def test_compile_scope_cold_goals_start_watchdog_after_admission(tmp_path, monkeypatch):
    monkeypatch.setenv('LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE', 'compile')
    now = [0.0]
    monkeypatch.setattr(goal_state.time, 'monotonic', lambda: now[0])
    source = 'theorem demo : True := by\n  trivial'
    document = goal_state.PreparedDocument('demo', tmp_path / 'Candidate.lean', tmp_path, source, 'supplied_environment', source, 0, source, 0)
    monkeypatch.setattr(goal_state, 'prepare_document', lambda *_: document)
    monkeypatch.setattr(goal_state.arena, 'persistent_quick_matches_project', lambda *_: False)

    @contextmanager
    def permit(*args, **kwargs):
        assert kwargs['timeout_seconds'] is None
        now[0] += 1000
        yield None

    class Session:
        startup_seconds, version = (0, 1)

        def __init__(self, *args):
            assert args[-1] == 10

        def start(self):
            assert self.request_deadline == 1010

        def open_document(self, _source):
            return (1, [])

        def interactive_goals(self, _position):
            return {'goals': [{'type': {'text': 'True'}, 'hyps': []}]}

        def close(self):
            pass
    monkeypatch.setattr(goal_state.arena.resource_gate, 'permit_from_environment', permit)
    monkeypatch.setattr(goal_state, 'GoalStateSession', Session)
    result = goal_state.query_goal_state(tmp_path / 'Task.json', document.candidate_path, tmp_path, line=2, column=None, timeout_seconds=10)
    assert result['rendered'] == '⊢ True' and result['backend'] == 'lsp'


@pytest.mark.parametrize("project_resident", [False, True])
def test_shared_source_document_preserves_changed_candidate_and_source_map(
    tmp_path: Path, project_resident: bool
) -> None:
    import json
    from dataclasses import FrozenInstanceError
    from lean_tools import lean_source, context_tools, oracle_search

    row = {
        "name": "Demo.target", "header": "import Lean\n\n", "contexts": [],
        "signature": "theorem target (h : True) : True",
        "src": "theorem target (h : True) : True := by trivial",
    }
    prefix = "import Lean\n\n"
    if project_resident:
        row["file_path"] = "Demo.lean"
        prefix = "module\nimport Lean\n\nnamespace Demo\n\ntheorem before : True := by trivial\n\n"
        (tmp_path / "Demo.lean").write_text(
            prefix + "/-- Target doc. -/\n" + row["src"]
            + "\n\ntheorem after : True := by trivial\nend Demo\n",
            encoding="utf-8",
        )
    task = tmp_path / "Task.json"
    task.write_text(json.dumps({"schema_version": 1, "row": row}), encoding="utf-8")
    declaration = row["signature"] + " := by\n  exact h"
    candidate_text = (
        lean_source.render_environment(row) + lean_source.TARGET_BEGIN
        + declaration + "\n" + lean_source.TARGET_END
    )
    candidate_path = tmp_path / "Candidate.lean"
    candidate_path.write_text(candidate_text, encoding="utf-8")
    snapshot = lean_source.snapshot_candidate(row, candidate_text, candidate_path)
    document = goal_state.prepare_document(task, candidate_path, tmp_path)
    assert document.source == prefix + declaration + "\n"
    assert context_tools.source_for_declaration(row, declaration, tmp_path) == document.source
    assert context_tools.target_prefix(row, tmp_path) == prefix
    assert oracle_search.exact_source_prefix(row, tmp_path).text == prefix
    assert "theorem after" not in document.source
    assert "/-- Target doc." not in document.source
    proof_offset = candidate_text.index("exact h")
    assert document.source_map().candidate_to_generated(proof_offset) == document.source.index("exact h")
    assert snapshot.declaration_start == candidate_text.index(declaration)
    row["signature"] = "theorem changed : False"
    row["contexts"].append({"src": "axiom unrelated : False"})
    assert snapshot.task.signature == "theorem target (h : True) : True"
    assert snapshot.task.supplied_environment == "import Lean\n\n"
    with pytest.raises(FrozenInstanceError):
        snapshot.declaration = "different"

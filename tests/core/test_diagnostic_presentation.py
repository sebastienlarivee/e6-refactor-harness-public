from __future__ import annotations
import json
from pathlib import Path
import pytest
from lean_tools import arena_workflow as arena
from lean_tools import diagnostic_presentation as presentation
from lean_tools import lean_goal_state as goals

def diagnostic(source, needle, *, severity='error', message='type mismatch'):
    position = goals.offset_to_lsp_position(source, source.index(needle))
    return {'severity': severity, 'message': message, **position}

def test_quick_and_goal_positions_agree_on_candidate_marker_and_unicode_column():
    declaration = 'theorem demo : True := by\n  have label := "😀"; exact missing'
    environment = 'import Lean\n\n'
    candidate = environment + arena.TARGET_BEGIN + declaration + '\n' + arena.TARGET_END
    generated = environment + declaration + '\n'
    raw = diagnostic(generated, 'missing')
    source_map = presentation.SourceMap.for_declaration(candidate, generated, declaration)
    mapped = presentation.map_diagnostic(raw, source_map)
    expected = goals.offset_to_human_position(candidate, candidate.index('missing'))
    assert mapped['location'] == {'scope': 'candidate', **expected}
    assert mapped['generated_position']['line'] == expected['line'] - 2
    assert mapped['generated_position']['character'] == expected['column']
    document = goals.PreparedDocument('demo', Path('Candidate.lean'), Path('.'), generated, 'supplied_environment', candidate, candidate.index(declaration), declaration, generated.index(declaration))
    goal_position, lsp = goals.map_candidate_position(document, **expected)
    assert goal_position == expected
    assert lsp == {key: raw[key] for key in ('line', 'character')}
    assert goals.map_diagnostic(goals.persistent.Diagnostic(**raw), document) == mapped
    text = arena.persistent_quick_diagnostic_text({'diagnostics': [raw]}, candidate_text=candidate, generated_source=generated, declaration=declaration)
    assert text.startswith(f'candidate:{expected['line']}:{expected['column']}: error:')

@pytest.mark.parametrize('exact', [False, True])
def test_project_prefix_and_same_line_measurement_wrapper_map_exact_spans(tmp_path, exact):
    declaration = 'theorem demo : True := by\n  have label := "😀"; exact missing'
    original = 'theorem demo : True := by trivial'
    source = 'module\npublic import Lean\npublic section\n\n/-- Removed target docs. -/\n' + original + '\n'
    (tmp_path / 'Demo.lean').write_text(source, encoding='utf-8')
    row = {'name': 'demo', 'file_path': 'Demo.lean', 'src': original, 'signature': 'theorem demo : True', 'header': 'import Lean\n', 'contexts': []}
    candidate = arena.render_environment(row) + arena.TARGET_BEGIN + declaration + '\n' + arena.TARGET_END
    generated = arena.project_compile_harness(row, declaration, tmp_path, exact=exact)
    assert 'Removed target docs' not in generated
    source_map = presentation.SourceMap.for_declaration(candidate, generated, declaration)
    for needle in ('theorem demo', 'missing'):
        raw = diagnostic(generated, needle)
        assert presentation.map_diagnostic(raw, source_map)['location'] == {'scope': 'candidate', **goals.offset_to_human_position(candidate, candidate.index(needle))}
    prefix = presentation.map_diagnostic(diagnostic(generated, 'module'), source_map)
    assert prefix['location'] == {'scope': 'generated', 'line': 1, 'column': 1}

def test_invalid_utf16_position_retains_generated_coordinates_without_guessing():
    declaration = 'theorem demo := "😀"'
    source_map = presentation.SourceMap.for_declaration(declaration, declaration, declaration)
    raw = diagnostic(declaration, '😀')
    raw['character'] += 1
    mapped = presentation.map_diagnostic(raw, source_map)
    assert mapped['location']['scope'] == 'generated'
    assert mapped['location']['column_encoding'] == 'utf-16'
    assert mapped['generated_position']['character'] == raw['character']

def test_cold_unicode_columns_and_lsp_utf16_columns_map_to_same_candidate():
    declaration = 'theorem demo := "😀" ++ missing'
    source_map = presentation.SourceMap.for_declaration(declaration, declaration, declaration)
    raw_lsp = diagnostic(declaration, 'missing')
    raw_cold = {**raw_lsp, 'character': declaration.index('missing')}
    assert presentation.map_diagnostic(raw_lsp, source_map)['location'] == presentation.map_diagnostic(raw_cold, source_map, position_encoding='unicode')['location']

def test_suggestion_replacement_maps_following_text_and_marks_replaced_text_as_anchor():
    declaration = 'theorem demo : True := by first | exact? | missing'
    candidate = '-- marker\ntheorem demo : True := by first | __LRH_SUGGEST__ | missing\n'
    generated = 'import Lean\n' + declaration + '\n'
    source_map = presentation.SourceMap.for_replacement(candidate, generated, declaration, '__LRH_SUGGEST__', 'exact?')
    mapped = presentation.map_diagnostic(diagnostic(generated, 'missing'), source_map)
    assert mapped['location'] == {'scope': 'candidate', **goals.offset_to_human_position(candidate, candidate.index('missing'))}
    anchor = presentation.map_diagnostic(diagnostic(generated, 'exact?'), source_map)
    assert anchor['location'] == {'scope': 'candidate', 'anchor': 'suggestion_marker', **goals.offset_to_human_position(candidate, candidate.index('__LRH_SUGGEST__'))}


def test_raw_artifact_retains_every_warning_and_generated_source(tmp_path):
    source = 'theorem demo : True := by trivial\n'
    source_map = presentation.SourceMap.for_declaration(source, source, source.strip())
    raw = [diagnostic(source, 'theorem', severity='warning', message='same warning') for _ in range(12)]
    shown = presentation.present_diagnostics(raw, source_map)
    path = presentation.archive_diagnostics(raw, shown, source=source, source_map=source_map, candidate_path=tmp_path / '.feedback' / 'sources' / 'snapshot.lean')
    artifact = json.loads(path.read_text(encoding='utf-8'))
    assert path.parent == tmp_path / '.feedback' / 'diagnostics'
    assert artifact['raw_diagnostics'] == raw
    assert len(artifact['mapped_diagnostics']) == 12
    assert artifact['diagnostics'][0]['count'] == 12
    assert artifact['generated_source'] == source

def test_quick_failure_archives_raw_diagnostics_and_uses_candidate_coordinates(tmp_path, monkeypatch):
    row = {'name': 'demo', 'header': 'import Lean\n', 'contexts': [], 'signature': 'theorem demo : True', 'src': 'theorem demo : True := by trivial', 'proof_length': 2}
    task = tmp_path / 'Task.json'
    task.write_text(json.dumps({'schema_version': 1, 'row': row}), encoding='utf-8')
    declaration = 'theorem demo : True := by exact missing'
    source = arena.render_environment(row) + arena.TARGET_BEGIN + declaration + '\n' + arena.TARGET_END
    candidate = tmp_path / 'Candidate.lean'
    candidate.write_text(source, encoding='utf-8')
    generated = arena.quick_compile_harness(row, declaration, tmp_path)
    raw = diagnostic(generated, 'missing')
    monkeypatch.setattr(arena, 'persistent_quick_matches_project', lambda _root: True)
    monkeypatch.setattr(arena, 'persistent_quick_request', lambda *_args: {'valid': False, 'wall_seconds': 0.1, 'diagnostics': [raw]})
    with pytest.raises(arena.LeanCompileError) as failure:
        arena._evaluate_candidate_uncached(task, candidate, tmp_path, quick=True)
    expected = goals.offset_to_human_position(source, source.index('missing'))
    assert f'candidate:{expected['line']}:{expected['column']}: error:' in str(failure.value)
    artifact = json.loads(Path(failure.value.result.log_path).read_text(encoding='utf-8'))
    assert artifact['raw_diagnostics'] == [raw]
    assert artifact['generated_source'] == generated

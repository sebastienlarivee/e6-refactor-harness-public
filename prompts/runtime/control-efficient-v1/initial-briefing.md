## This pass

{{starting_instructions}}
{{incumbent_briefing}}
## Fixed task and environment

- Task: {{task_id}}. The exact statement, imports, and ordered contexts are in Candidate.lean and Task.json.
- Primary project: `{{primary_project}}`.
- Target source: `{{primary_project}}/{{target_relative_path}}`. Source directory: `{{primary_project}}/{{target_relative_directory}}`.{{source_visibility_notice}}
- Fixed scoring denominators: `T0 = {{original_tokens}}` local tokens and `H0 = {{original_heartbeats}}` heartbeats, retained across passes.{{original_control_measurement_line}}
- Compatibility: the primary environment plus {{compatibility_count}} supplied alternate versions, {{total_version_count}} environments in total.
- Starting Candidate.lean SHA-256, over its full UTF-8 source: `{{candidate_sha256}}`. Refresh it after edits; returned hashes and goal handles belong to specific snapshots.

{{score_sensitivity}}

Core native tools are lean_feedback.edit_check, lean_feedback.score_candidate, lean_feedback.compare_candidates, lean_feedback.unfinished_cases, and lean_feedback.profile_proof. COMMANDS.md explains their mutation, measurement, checkpoint, inspection, and profiling behavior, plus the shell fallbacks. Read the proof, choose a promising idea, and test it.

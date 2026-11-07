# Useful commands

Use the core native tools `lean_feedback.edit_check`,
`lean_feedback.score_candidate`, `lean_feedback.compare_candidates`,
`lean_feedback.unfinished_cases` and `lean_feedback.profile_proof`.
Run Lean through these tools or the documented wrappers so it shares the
experiment's cached environments and resource gate. Do not invoke `lean` or
`lake env lean` directly. When calling native tools from JavaScript, await the
tool promise before the execution context ends. If execution yields a running
cell ID, use the host's wait tool to collect its result.

## Choose feedback for the experiment

Use the supplied hash and verified measurements. Inspect focused source ranges
and relevant command sections; avoid broad startup reads or remeasuring an
unchanged host-verified proof.

- Predictable complete change: call `score_candidate` directly with the current
  `expected_sha256` and `body` or unique-match `edits`. It validates the proposed
  source and measures all three score axes without pruning or editing the draft.
  A separate quick check of the same source is unnecessary.
- Independent complete variants: use one `compare_candidates` request below.
- Uncertain structural change or dependent repair: use `edit_check(mode="quick")`,
  then choose the next edit from diagnostics or goals. Score a complete promising
  proof when ready; avoid repeating checks on an unchanged scored snapshot.

Keep the best measured checkpoint and explicitly restore or promote it if chosen;
host selection remains authoritative. Spend saved round trips on further proof
experiments within the host's budget; a working proof or plateau is not a reason
to end the search.

## Independent candidate comparisons

`lean_feedback.compare_candidates` accepts the current full-source
`expected_sha256` and two to four `alternatives`, each with a distinct short ASCII
`label` and exactly one `body` or unique-match `edits` list. Replace these proof
placeholders:

```json
{"expected_sha256": "{{candidate_sha256}}", "alternatives": [
  {"label": "direct", "body": "by\n  <complete first proof>"},
  {"label": "lemma", "body": "by\n  <complete independent second proof>"}
]}
```

Every alternative starts from the same immutable base; its own edits apply in
order. A batch never combines variants, edits the draft or promotes a winner.
Batch only independent ideas that need no intermediate feedback; use sequential
checks for dependent repairs. One alternative's failure does not erase valid
neighbors.

All variants receive primary validation; exact-valid proofs retain immutable
checkpoints. A strict optimistic loser may skip compatibility, returning
`valid_pruned`, `compatibility_status="skipped_optimistic_bound"` and no complete
score. Incomplete compatibility also yields no score. `ranking` and `best_label`
compare only scored rows; `best_label=null` means none were fully scored. An
optimistic bound, token count, fewer goals or checkpoint alone is not a measured
combined-score improvement. Inspect failures and unscored rows as needed.

To fully measure a retained checkpoint without pruning, call
`score_candidate(checkpoint_id=...)` with the current draft's `expected_sha256`.
Explicitly restore or promote your choice; the host revalidates it.

`edit_check` modes:

| Mode | Evidence |
| --- | --- |
| `quick` (default) | Primary compilation, local tokens and an immutable valid checkpoint. No new exact heartbeat measurement or axiom audit; a cached exact heartbeat may be returned explicitly. |
| `advisory` | A warm heartbeat estimate for guidance; no accepted checkpoint. |
| `exact` | Exact primary heartbeats, tokens, allowed-axiom audit and checkpoint. No compatibility score. |

## Source identity, edits and checkpoints

`expected_sha256` is the 64 lowercase hex SHA-256 of the current candidate's
complete UTF-8 bytes. The starting hash is `{{candidate_sha256}}`; refresh it
after editing. It binds the current destination, even when a checkpoint supplies
the source being tested.

For `edit_check` and `score_candidate`, omit mutations to check the current
draft, or supply at most one of:

- `body`: complete proof text after `:=`, such as `by ...`.
- `edits`: `{"old": "...", "new": "..."}` pairs, applied in order; each
  `old` string must match exactly once.
- `source_text`: literal complete Lean source, never a pathname. The legacy
  `source` alias has the same meaning.

An optional `checkpoint_id` loads an immutable saved checkpoint as the base;
it can be used alone or with one mutation above. Preserve the signature and
frozen context in every form.

The tools differ in what they write:

- `edit_check` updates the selected draft **before** evaluating an immutable
  snapshot. If evaluation fails, the edited draft stays in place; it does not
  roll back. Supply `expected_sha256` when replacing or restoring source.
- `score_candidate` leaves the draft unchanged, even when given an alternative
  body, edits, source or checkpoint. Its results identify the evaluated snapshot
  and, when exact-valid, its immutable checkpoint. Explicitly restore or promote
  that checkpoint if you choose it.

For an alternate draft, set `candidate` to its capsule filename. Returned source
hashes and `goal_id` handles identify the evaluated snapshot, not any later edit.

To return to your best saved source, use `edit_check` with `checkpoint_id`,
the current destination's `expected_sha256`, and either:

- `mode="quick"` or `mode="exact"` to copy it into the draft and evaluate it;
- `operation="restore"` to copy it unchanged without evaluation.

Other copy operations are `operation="promote"`, which targets `Candidate.lean`,
and `operation="clone"`, which requires a distinct `candidate` filename and may
apply a mutation to the checkpoint. Restore/promote cannot include mutations.
Copy operations omit `mode` and `goal`; they report
`evaluation_status="not_run"`. Existing destinations require their current
`expected_sha256`. A copy is not fresh validation.

## Long calls and response recovery

Each admitted feedback request records a request ID and durable receipt under
`.feedback/requests/` before waiting for its turn. `phase="queued"` means it has
been accepted but has not begun; `phase="in_progress"` means execution has
started. `queue_wait_seconds` separates that wait from execution. Queued work
checks a supplied `expected_sha256` when it starts, so a later source change can make it
stale. Avoid concurrent edits while work is queued or in progress.

`feedback_request.request_id` identifies the durable request. Legacy replies also
include its receipt/result paths; compact replies link the full result through
`full_response_path`. Large inline feedback carries explicit truncation metadata.
Compact results may also link `full_response_path`; use their verdict, hash and
checkpoint ID routinely, and read focused details as needed. Presentation does
not change validation or receipts.
Exact-failure diagnostics map to candidate lines when reliable; `generated_source_path` links preserved generated
source for other locations, and `compiler_log_path` retains the full compiler log.

If a native call appears to have no completion, inspect requests from a separate
shell call, even while another request is queued or the MCP worker is busy:

```sh
{{python}} {{tools_root}}/feedback_requests.py --root {{capsule}} --limit 5
```

Add `--request-id <returned-request-id>` to inspect one request. The receipt
separates execution status, source hashes, and response write status. A successful
write does not prove the model received the result. Read a completed result before
retrying; a queued request is still pending work.
An `unknown` owner state means process visibility is insufficient to determine
whether the owner is running; it does not establish that work stopped.
This status command is read-only and does not cancel work.

## Unfinished cases and optional profiling

When Lean reports unsolved goals, failed `edit_check` calls try to include a
bounded menu of the remaining cases.
Inspect a stalled case with `unfinished_cases` using the current
`expected_sha256` and its returned `goal_id`; the response gives that case's
target and local hypotheses. Omit `goal_id` to list cases (default `limit=6`,
maximum 12). Automatic failed-edit extraction has a 15-second limit. An explicit
`unfinished_cases` request defaults to 60 seconds (`0 < timeout_seconds <= 60`),
so it can retry a cold extraction that timed out. Successful source-bound
contexts are reused. To inspect a known interior goal, `edit_check` accepts
`goal` with one-based candidate line/column coordinates and returns handles for
that snapshot. Use known coordinates rather than guessed line numbers.

When a compiling proof's elaboration costs are unclear, `profile_proof` can
help choose the next change. It is optional; keep routine iterations quick.

{{profiler_capability_summary}}

For profiling, `expected_sha256` binds the selected candidate or checkpoint
source. A checkpoint request uses that checkpoint's hash. Stage timings and
validation-cache status distinguish cold validation from profiling work. A
complete result requires measured, contained regions; repeated, missing, or
inconsistent measurements are reported explicitly. Profiling is advisory and
never accepts a proof or changes its score.

```json
{"expected_sha256": "{{candidate_sha256}}", "mode": "regions"}
```

By default this profiles the unique outermost parsed tactic sequence in the
proof body, including a nested `by` in a term or lambda proof such as
`fun x => by ...`. Multiple independent outermost tactic sequences need an
explicit selection; a pure term proof has no tactic region.

To focus on a crucial step, add
`"regions": [{"text": "<exact unique tactic or tactic block>"}]`.
Text must occur exactly once in the complete source; a partial tactic or an
arbitrary substring spanning several tactics is unsupported. Ambiguous or
unsupported selections return `region_menu` with up to 16 parsed choices, their
`original_span`, and copyable `selector` objects. Put up to 8 of those selectors
in `regions` with the same `expected_sha256`; choices must be distinct and
disjoint or nested. The menu identifies syntax, not successful measurements.

Region costs include nested work and remain advisory. `mode="wall_time"` instead
groups summed native thread-slice costs by tactic kind without source-line
attribution. Validate a chosen change with complete scoring; use a quick check first when
its correctness is uncertain.

## Shell fallbacks

These POSIX commands use the task, candidate, checkpoint directory and inherited
broker from `feedback-config.json`. Quick checks share a 60-second wall allowance
across queue, locks, compilation and optional diagnostics, plus bounded cleanup.
A timeout is inconclusive and is never replayed cold automatically. If a slow
check is justified, retry explicitly with `"timeout_seconds": 600` (or a smaller
allowance up to the capsule maximum). Exact scoring retains its configured
600-second per-process allowance. These commands check the current file:

```sh
printf '%s\n' '{"mode":"quick"}' | {{python}} {{tools_root}}/feedback_workflow.py --config {{capsule}}/feedback-config.json
printf '%s\n' '{"mode":"advisory"}' | {{python}} {{tools_root}}/feedback_workflow.py --config {{capsule}}/feedback-config.json
printf '%s\n' '{"mode":"exact"}' | {{python}} {{tools_root}}/feedback_workflow.py --config {{capsule}}/feedback-config.json
```

The JSON accepts the same `body`, `edits`, `goal`, `candidate`, source and
checkpoint fields as the native tool. For multiline edits, write a request JSON
file and redirect it into the same Python command with `< request.json`.

Complete score for the current draft:

```sh
printf '%s\n' '{"expected_sha256": "{{candidate_sha256}}"}' | {{python}} {{tools_root}}/feedback_workflow.py --config {{capsule}}/feedback-config.json --tool score_candidate
```

For a batch, send the same comparison JSON above to the wrapper with
`--tool compare_candidates`; write multiline JSON to a request file and use
`< request.json`. Each candidate's quick screen has its own 60-second wall
allowance; exact scoring and compatibility keep their configured process
allowances. The complete batch can therefore take longer than one quick check.

For goal inspection or profiling, use the same wrapper with
`--tool unfinished_cases` or `--tool profile_proof` and that tool's JSON arguments.
Their extraction and profiling limits are described above.

Direct evaluator commands take an explicit timeout:

- quick validation, local tokens, and immutable checkpoint: `{{python}} {{tools_root}}/arena_workflow.py evaluate --task {{capsule}}/Task.json --candidate {{capsule}}/Candidate.lean --project-root {{primary_project}} --fingerprint-registry {{capsule}}/environment-fingerprints.json --checkpoint-dir {{capsule}}/valid-candidates --timeout 60 --quick`
- exact primary heartbeat and axiom measurement: `{{python}} {{tools_root}}/arena_workflow.py evaluate --task {{capsule}}/Task.json --candidate {{capsule}}/Candidate.lean --project-root {{primary_project}} --fingerprint-registry {{capsule}}/environment-fingerprints.json --checkpoint-dir {{capsule}}/valid-candidates --timeout 600 --json-output {{capsule}}/latest-exact.json`

## Scratch and source access

For `#check` or other scratch work, create `Scratch.lean` and run:
`{{python}} {{tools_root}}/arena_workflow.py lean-file --path {{capsule}}/Scratch.lean --project-root {{primary_project}} --timeout 600`

Narrow read-only source searches may inspect only:

{{source_search_roots}}

For example: `grep -R -n --include='*.lean' -- '<pattern>' {{source_search_root_arguments}}`.

Respect the task's source visibility boundaries and legal prefix. Alongside the
evaluator and feedback wrappers above, the following arena-safe discovery files
are the only additional out-of-capsule helpers you may execute. They emit JSON
stdout:

- capability intersection: `{{python}} {{tools_root}}/context_tools.py capabilities --task {{capsule}}/Task.json --project-root {{primary_project}}{{compatibility_root_arguments}} --fingerprint-registry {{capsule}}/environment-fingerprints.json --timeout 600`
- theorem-entry suggestion sweep: `{{python}} {{tools_root}}/context_tools.py suggest --task {{capsule}}/Task.json --project-root {{primary_project}}{{compatibility_root_arguments}} --fingerprint-registry {{capsule}}/environment-fingerprints.json --timeout 600`
- goals/hypotheses: `{{python}} {{tools_root}}/lean_goal_state.py --task {{capsule}}/Task.json --candidate {{capsule}}/Candidate.lean --project-root {{primary_project}} --line <one-based-line> --pretty --timeout 600`
- prefix-bounded declaration search: `{{python}} {{tools_root}}/oracle_search.py search --task {{capsule}}/Task.json --project-root {{primary_project}} --name-query "map" --limit 20 --timeout 600`
  Add `--type-query "Finset"` to filter rendered declaration types.
  Search limits are frozen by the host:
  `1 <= --limit <= --candidate-limit <= 30`; both defaults are 30.
  Frozen ranking is `baseline`; omit `--ranker` and `--model`.
- optional cached Aesop sidecar: `{{python}} {{tools_root}}/oracle_search.py aesop --task {{capsule}}/Task.json --project-root {{primary_project}} --fingerprint-registry {{capsule}}/environment-fingerprints.json --timeout 600 --candidate-output {{capsule}}/AesopCandidate.lean`{{compatibility_oracle_fallback}}

For suggestions at an interior goal, put one `__LRH_SUGGEST__` marker in a
disposable candidate copy and pass it with `--candidate`. Never leave the marker
in the real candidate. Aesop output is usable only when `pristine_replay.valid`
is true; it still requires normal exact and cross-version evaluation. No
scratch-only import, tactic, declaration or generated helper may remain in the
final proof.

# Objective

Find the strongest verified proof of {{task_id}} you can in this pass. Optimize the combined score across proof tokens, exact primary heartbeats, and version compatibility. The theorem and legal environment are fixed; the argument used to prove it is yours to redesign.

## Be ambitious about the proof

Search for substantial improvements even when a proof already looks short or polished. A working proof is a valuable fallback, not a reason to keep its structure. You may replace the entire body, discard intermediate steps, or pursue a different mathematical argument. Prefer a change that removes a source of complexity over prolonged polishing of its symptoms.

Look for meaningfully different ways to solve the theorem. Could an available general lemma replace a chain of steps? Would another formulation, representation, decomposition, induction, or local intermediate fact make the goal simpler? Could a direct term or focused rewrite avoid expensive automation? Choose ideas that fit the actual statement and legal context; these are possibilities to investigate, not a prescribed sequence.

## Learn through quick experiments

Keep planning brief and make the next experiment concrete. Identify the crucial step of an approach and test it before building a long proof around it. Use Lean's goals and errors to refine the idea. Use sequential quick feedback for uncertain changes and dependent repairs. Send predictable complete changes directly to `score_candidate`; compare independent complete variants with `compare_candidates`. COMMANDS.md explains scoring and batch contracts.

For a stalled case, inspect its local goal and test the crucial step in that context. Profile a valid proof when unclear elaboration costs could guide the next change; keep routine iterations quick.

When repeated edits encounter the same obstacle, reconsider the underlying argument or seek a more useful lemma. Repeating cosmetic variations is not a new approach. Revisit a blocked route when you have a specific new idea or evidence that changes its prospects. Use focused source inspection when it can answer a concrete question. Reuse supplied hashes and verified measurements; avoid repeated instruction reads and broad startup discovery.

If you lack a verified proof, secure a valid fallback promptly; then challenge your best candidate. Do not stop merely because the first candidate compiles, or leave a credible improvement for a hypothetical later pass. Spend effort where there is plausible score upside, and reserve enough attention to measure and leave your best complete proof. Keep any working notes brief and useful for choosing the next experiment.

## Preserve the best result

Keep verified checkpoints while exploring. A failed edit can leave the working file invalid; restore a known checkpoint when you need a valid starting point. Compare complete combined scores rather than text length or advisory estimates alone. Before finishing, put your strongest verified choice in Candidate.lean. Report the chosen result briefly, with any unresolved validation limitation stated accurately.

## Workspace and execution

Work independently. Use this capsule, the supplied cached project sources, and the documented tooling. Run Lean through the wrappers in COMMANDS.md so it uses the shared resource queues. Do not use children or subagents, web access, prior session history, archives, previous experiment solutions, parent or sibling directories, or unrelated files. The legal proof boundary is defined in LEAN_PROOF_GUIDE.md.

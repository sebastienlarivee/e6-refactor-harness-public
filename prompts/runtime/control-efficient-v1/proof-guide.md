# Proof and scoring reference

Prove the same theorem while improving its combined score. Change only the proof
body after `:=`. Preserve the exact theorem signature, frozen header, ordered
contexts and surrounding scaffold. Use declarations available in the legal source
prefix and supplied libraries; the target theorem and later source declarations
are not available to prove the target. Within the body, you may replace the whole
argument, switch between term and tactic proofs, and introduce local `have` or
`let` helpers. Ordinary classical reasoning is allowed.

## Validity

The proof must compile in the primary environment and pass the exact axiom audit.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed axiom dependencies.
Do not add imports or top-level declarations, `sorry`/`admit`, new axioms, unsafe
declarations or terms, `native_decide` or other reduction oracles, IO, kernel
bypasses, implementation overrides, or elaborator/macro extensions. Scratch
discoveries must produce an ordinary proof in the frozen context; scratch-only
imports and helpers cannot remain in the submitted proof.

The complete submitted theorem declaration, including its signature and comments,
must contain at most **262144 Unicode characters**. The surrounding scaffold is
excluded.

## Three equally weighted score axes

Let `T` be the candidate's local proof-token count, `H` its exact primary
heartbeats, and `P` the number of supplied Lean versions that pass, including the
primary version. The fixed original denominators remain
`T0 = {{original_tokens}}` and `H0 = {{original_heartbeats}}` across passes.

```text
token_reduction     = round(100 * (T0 - T) / T0, 2)
heartbeat_reduction = round(100 * (H0 - H) / H0, 2)
compatibility       = 100 * P / {{total_version_count}}
combined_score      = round((token_reduction + heartbeat_reduction + compatibility) / 3, 4)
```

Reductions are not clamped: a longer or more expensive proof contributes a
negative reduction. Compatibility is a score component; failing an alternate
version lowers that component rather than invalidating an otherwise valid
primary proof. Missing or incomplete measurements do not receive a score. On a
tied combined score, the host keeps the verified incumbent.

## Evidence and final choice

Use `score_candidate` directly for predictable complete changes, independent
`compare_candidates` batches when useful, and sequential quick checks when
uncertainty needs diagnostics. Only complete measurements establish the score. Quick checks establish primary
compilation and count tokens; advisory observations estimate heartbeats. Neither
substitutes for exact heartbeats, the axiom audit and compatibility measurements.
An `edit_check(mode="exact")` measures primary heartbeats and axioms but does not
measure the complete score. A batch's pruned optimistic bound is not a score;
see COMMANDS.md for checkpoint and ranking contracts.

Keep a known valid checkpoint while exploring. Restore or promote the best
measured choice to `Candidate.lean` before finishing. The host revalidates saved
candidates and makes the final selection. See `COMMANDS.md` for tool contracts,
restoration and optional discovery.

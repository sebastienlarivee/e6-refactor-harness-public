# OpenRouter execution

Pass a funded OpenRouter API key through `./run.sh --api-key-file /absolute/private/openrouter.key`. Keep that file private (`0600`) and outside the release, runs and prepared projects.

Host workers retain the real key. Isolated proof agents receive proof-specific loopback access, and each proof keeps its own persistent actual-cost ledger across passes and resume. The included model/provider policy is supplied by the release.

The USD 2.90 spending threshold leaves a USD 0.10 buffer for the final request. All 60 submitted proof attempts stayed below the contest's USD 3 cap. Reported cache discounts and separately billed BYOK inference count toward spending. Missing generation receipts are retried automatically; an optional exclusive-run-key policy permits one audited presumed-zero recovery. Provisional costs stay visible and correctable. See [spending and recovery](../../docs/operations.md#automatic-recovery).

Use the [README](../../README.md) to set up, run all 60 proofs, monitor progress and collect the verified local JSONL result.

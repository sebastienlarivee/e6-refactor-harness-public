# Lean environments

The bundle supplies an environment manifest covering the complete benchmark, with exact upstream commits for each project and its dependencies. The exact native Lean toolchains must already be installed in the elan home used by setup.

`./setup.sh` downloads those pinned sources, prepares them using matching compiled caches and targeted builds, then records explicit environment paths. Source downloads are reused across project versions, while each version has its own build directory. The run's preflight checks the pinned compiler/project identities, recursive imports and original proofs before inference.

Setup uses the pinned project revisions and Lake manifests. Preserve the prepared roots and toolchains through execution, resume and export. Candidate proofs and helper caches use the run's writable working area.

See [setup](setup.md) for host prerequisites and elan-path selection.

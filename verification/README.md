# Verification records

`comparator-result.json`, `comparator.log`, `definition-identity.json`, and
`package-audit.json` are unchanged records of the original release, before the
submission cleanup. They report acceptance of `ThresholdChallenge.main` by all
three kernels and exact identity of the frozen definitions. The corresponding
source snapshot is commit `96711ddb0061feb9726ae80e394941dcd8a18f31`.

`source-audit.json` records the current static source checks and cleanup
inventory. `release-source.sha256` contains the current Lean-source and
configuration hashes. The canonical `Challenge.lean` and its definitions-only
companion remain byte-for-byte unchanged.

`donor-audit.json` records the source comparison against the pinned OpenAI and
Anthropic reference repositories and the helper-level credits listed in NOTICE.

Lean, Lake, the Comparator, and the kernels have not been rerun for this cleanup.
Running the command documented in the repository README will write new records
under `verification/comparator/`.

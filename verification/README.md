# Verification records

## Current release: clean rebuild and Comparator after the cleanup

`rebuild/` and `comparator/` record a clean rebuild and a three-kernel Comparator run of the source tree of commit
`8a16d28`. The run happened on 2026-10-28 between 11:31 and 11:38 UTC, on an Ubuntu workstation. Lean is
`v4.35.0-rc2` and Mathlib is `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The script that made it is
`rebuild/clean4.sh`.

- `rebuild/summary.txt` gives the verdict lines.
  - The fresh checkout had 0 project `.olean` files.
  - `lake exe cache get` exited 0.
  - `lake --no-cache build` exited 0: "Build completed successfully (9377 jobs)", 444 project modules compiled.
- `rebuild/axioms.log` gives `#print axioms ThresholdChallenge.main` in the Solution environment:
  `[propext, Classical.choice, Quot.sound]`. The two-line probe file, written by the script as `Axioms.lean`, is
  kept as `rebuild/Axioms.lean.txt`, so that every `.lean` file in the package is a hashed package source.
- `comparator/comparator-result.json` and `comparator/comparator.log` hold the run of `scripts/run_comparator.py`.
  - con-ron `--verified` accepted 57,450 declarations.
  - All three kernels accept the solution: con-ron, NanoDa and Lean's default kernel. The transcript ends with
    `Your solution is okay!`.
  - The two kernel exports (73 MB and 451 MB) are not checked in. Their sizes and SHA-256 hashes are in
    `comparator-result.json`.
- `release-source.sha256` hashes all 444 `.lean` files of the package and the four toolchain, dependency, build and
  Comparator configuration files of this release. The 444 files are the `ThLean/` modules, `ThLean.lean`,
  `Challenge.lean` and `Solution.lean`.

## Earlier records

- `comparator-result.json`, `comparator.log`, `definition-identity.json` and `package-audit.json` at this level are
  the records of the original release, commit `96711ddb0061feb9726ae80e394941dcd8a18f31`, before the cleanup.
  `definition-identity.json` shows that the 19 compiled companion declarations equal the frozen definitions.
  `Challenge.lean` and `ThLean/Challenge/MainDefinitions.lean` are byte-for-byte unchanged since then.
- `source-audit.json` records the static source checks and the cleanup inventory of commit `db93094`.
- `donor-audit.json` records the comparison against the pinned OpenAI and Anthropic reference repositories and the
  helper-level credits listed in `NOTICE`.

After `db93094`, commit `8a16d28` changed docstrings in five Lean files and changed the README. It changed no Lean
code.

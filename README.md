# q-colorability threshold: Lean formalization (Palomar package)

Lean 4 formalization of the two headline theorems of P. M. Aronow and Patrick Lopatto,
*Existence of the q-Colorability Threshold for Sparse Random Graphs*:

- **Theorem 1.1.** For every integer q ≥ 3 there is α_q ∈ [1/2, γ_q], where
  γ_q = log q / log(q/(q−1)), such that P(G(n, ⌊cn⌋) is q-colorable) tends to 1
  for fixed 0 ≤ c < α_q and to 0 for fixed c > α_q. Likewise,
  P(G(n, d/n) is q-colorable) tends to 1 for fixed 0 ≤ d < 2α_q and to 0
  for fixed d > 2α_q.
- **Theorem 1.2.** For the same α_q and every η ∈ (0, 1), there are C > 0,
  an integer n₀ ≥ 2q, and integers m_n with m_n/n → α_q such that, for n ≥ n₀,
  the first loss H of q-colorability in the multigraph edge process satisfies
  |H − m_n| ≤ C n (log n)^(−3/2) with probability at least 1 − η.

The edge process samples independent uniform unordered pairs of distinct vertices
with replacement and retains repeated edge occurrences. G(n, d/n) has its usual
probability interpretation for positive n and 0 ≤ d ≤ n; for each fixed d ≥ 0,
this holds for all sufficiently large n. No conclusion is asserted at the threshold.

`ThresholdChallenge.MainStatement` in `Challenge.lean` combines both results under
one existential threshold. `Solution.lean` supplies the closed theorem
`ThresholdChallenge.main`. The Challenge imports only Mathlib. The Solution's
442-file local import closure excludes the Challenge's deliberate theorem placeholder.
The permitted axioms are exactly `propext`, `Quot.sound`, and `Classical.choice`;
there are no definition holes.

## Manuscript and fidelity

[Read the manuscript (PDF)](Aronow_Lopatto_colorability_threshold.pdf).
The [LaTeX sources](paper/) include the figures, bibliography, and local style file.
To regenerate the PDF with a standard TeX installation:

```bash
cd paper
latexmk -pdf -outdir=build main.tex
```

The Lean statement was written from the frozen draft of 2026-10-27. The included
manuscript has the same headline statements. Its ε is the Challenge's η, and
`n₀ ≥ max 3 (2q)` is equivalent to `n₀ ≥ 2q` for q ≥ 3.
The formalization covers these two theorems, rather than every remark and
literature statement in the manuscript.

[The fidelity audit](verification/submission/fidelity.md) records the comparison
of models, quantifiers, probability normalizations, hitting-time indexing, and
window rounding. `scripts/check_finite_models.py` supplies independent exact
finite-model sanity checks. These checks supplement the Lean proofs.

All 444 project Lean files use the module system. The submission port adds public
imports, exposed public declarations, and four explanatory definition docstrings;
`scripts/audit_submission.py` checks that every mathematical token agrees with the
original package after removing only the port syntax and comments. The Challenge
and its definitions-only companion are textually identical after removing the
final theorem and its docstring. Comparator also checks their compiled declarations.

## Reproduce verification

Use the committed `lean-toolchain` and `lake-manifest.json`, and Python 3.11 or newer
for the verification scripts:

```bash
lake exe cache get
lake --no-cache build
python3 scripts/audit_submission.py
python3 scripts/check_finite_models.py
python3 scripts/run_comparator.py --package . --report verification --label local-check
sha256sum -c verification/release-source.sha256
```

Choose a fresh report label for each run. The runner requires the selected Lean
toolchain's `leanexport`, `leanchecker`, and `nanoda_bin`; it also runs con-ron in
verified mode when available. `--con-ron /path/to/con-ron` selects an explicit
checker. Palomar currently specifies a newer con-ron binary for this Lean release
in its [checker revisions](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/checker-revisions.json).
The checked-in current report records the actual tool paths and binary hashes.

The submitted `comparator.json` uses Palomar's restricted schema. The local runner
adds checker commands only to a temporary execution configuration. Its export
files are omitted from Git; their sizes and hashes remain in the result record.
This local reproduction is separate from Palomar's protected verification workflow.
See [verification records and their scope](verification/README.md).
For the official static validators, install the requirements of a checkout of
[PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission) and run:

```bash
python3 scripts/check_palomar.py --palomar-submission /path/to/PalomarSubmission \
  --licensee-bundle /path/to/bundle --json-output verification/local-static.json
```

The Bundler executable must have PalomarSubmission's locked Licensee dependencies
installed; this enables the exact SPDX licence detector as well as the source,
configuration, dependency, and metadata checks.

## Submission inputs

Use repository `pmaronow/q-colorability-palomar`, the full 40-character SHA of the
prepared commit, configuration path `comparator.json`, and metadata path
`formalization.yaml`. Leave the project directory blank for the repository root.
The repository must be public before Palomar can read it; this preparation does
not change its visibility.

`formalization.yaml` records the author-confirmed human authors and responsible
maintainers, P. M. Aronow and Patrick Lopatto, and material AI tools Opus 5.5,
Luna 6, and GPT Sol 6.1. Source and release history are retained in
`provenance.json`. Original frozen-source hashes and earlier verification records
remain historical evidence, rather than claims about unchanged current bytes.

## Licence

The original project Lean sources and scripts are licensed under the
[MIT License](LICENSE), copyright (c) 2026 P. M. Aronow and Patrick Lopatto.
Third-party material and dependencies retain the licences and attributions
listed in [NOTICE](NOTICE). This grant does not cover the manuscript PDF or
LaTeX sources. The [donor-source audit](verification/donor-audit.json) records
comparison scope, credited helper patterns, source locations, and limits of review.

# q-colorability threshold: Lean formalization (Palomar package)

Lean 4 formalization of the two headline theorems of P. M. Aronow and Patrick Lopatto, *Existence of the
q-Colorability Threshold for Sparse Random Graphs*. The Lean statement was written from the frozen draft of
2026-10-27. Theorems 1.1 and 1.2 of the manuscript included below have the same mathematical content; that version
writes ε for η, says explicitly that c and d are fixed reals ≥ 0, and explicitly takes n₀ to be an integer with
n₀ ≥ 2q (`Challenge.lean` requires n₀ ≥ max 3 (2q)):

- **Theorem 1.1.** For every integer q ≥ 3 there is α_q ∈ [1/2, γ_q], γ_q = log q / log(q/(q−1)), such that
  P(G(n, ⌊cn⌋) is q-colorable) → 1 for 0 ≤ c < α_q and → 0 for c > α_q, and
  P(G(n, d/n) is q-colorable) → 1 for 0 ≤ d < 2α_q and → 0 for d > 2α_q.
- **Theorem 1.2.** For the same α_q and every η ∈ (0, 1) there are C > 0, n₀ and integers m_n with m_n / n → α_q
  such that, for n ≥ n₀, the hitting time H of non-q-colorability in the multigraph edge process satisfies
  |H − m_n| ≤ C n (log n)^{−3/2} with probability at least 1 − η.

The edge process draws independent uniform unordered pairs of distinct vertices
with replacement, retaining repeated edge occurrences. The binomial model
G(n, d/n) is interpreted for positive integers n and 0 ≤ d ≤ n; for each fixed
d ≥ 0, this condition holds for all sufficiently large n.

Both are the single statement `ThresholdChallenge.MainStatement` in `Challenge.lean` (Mathlib only, 125 lines).
`Solution.lean` supplies `ThresholdChallenge.main` with no `sorry`. Before the
source cleanup, the Comparator accepted the proof with con-ron `--verified`,
NanoDa, and Lean's default kernel, using only `propext`, `Quot.sound`, and
`Classical.choice`. The checked-in records under `verification/` describe that
run. The current cleanup has been checked statically; Lean and the Comparator
have not been rerun after the import changes.

## Manuscript

[Read the manuscript (PDF)](Aronow_Lopatto_colorability_threshold.pdf).
The [LaTeX sources](paper/) include all figures, the bibliography, and the local style file.
To regenerate the PDF with a standard TeX installation:

```bash
cd paper
latexmk -pdf -outdir=build main.tex
```

The formalization targets the two headline theorems above. The manuscript also
contains explanatory remarks and discussion of related work.

## Release

`Challenge.lean` is the verbatim frozen 125-line headline challenge, with SHA-256
`037fe846ca2426d2d0f87527ce9618ce6a510099013691f8cd5c649093294856`.

`Solution.lean` imports the definitions-only companion through the project Bridge
and ends with:

```lean
theorem ThresholdChallenge.main : ThresholdChallenge.MainStatement := ThLean.Final.main
```

The recorded comparison found that all 19 compiled companion declarations,
including generated helpers, have exactly the same names, universe parameters,
types, and values as the frozen definitions. Both source files are unchanged.
The Solution's 442-module local import closure excludes the frozen theorem stub.
The permitted axioms in `comparator.json` are exactly `propext`, `Quot.sound`, and `Classical.choice`.
The definition-exemption list is empty.

Reproduce with the pinned Lean toolchain and dependency manifest:

```bash
lake exe cache get
lake build
python3 scripts/run_comparator.py --package . --report verification --label comparator
sha256sum -c verification/release-source.sha256
```

The runner writes its records and exports under `verification/comparator/`,
exports the Challenge and Solution, and invokes `lake comparator` with its
sandbox enabled. The requested kernels are `con-ron --verified`, NanoDa, and
Lean's default kernel (`leanchecker`). Success requires all three acceptance
markers and `Your solution is okay!`.

`verification/package-audit.json` records the original release's source hashes,
dependency revisions, and static import closure. The current source checks and
cleanup inventory are in `verification/source-audit.json`.
`verification/release-source.sha256` covers the current Lean sources and the four
toolchain, dependency, build, and Comparator configuration files.

## Licence

The original project Lean sources and scripts are licensed under the
[MIT License](LICENSE), copyright (c) 2026 P. M. Aronow and Patrick Lopatto.
Third-party material and dependencies retain the licences and attributions
listed in [NOTICE](NOTICE). This grant does not cover the manuscript PDF or
LaTeX sources.
The [donor-source audit](verification/donor-audit.json) records the comparison
scope, matching helper patterns, source locations, and limits of the review.

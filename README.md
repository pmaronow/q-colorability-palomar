# q-colorability threshold: Lean formalization (Palomar package)

Lean 4 formalization of the two headline theorems of P. M. Aronow and Patrick Lopatto, *Existence of the
q-Colorability Threshold for Sparse Random Graphs* (frozen draft of 2026-10-27):

- **Theorem 1.1.** For every integer q ≥ 3 there is α_q ∈ [1/2, γ_q], γ_q = log q / log(q/(q−1)), such that
  P(G(n, ⌊cn⌋) is q-colorable) → 1 for 0 ≤ c < α_q and → 0 for c > α_q, and
  P(G(n, d/n) is q-colorable) → 1 for 0 ≤ d < 2α_q and → 0 for d > 2α_q.
- **Theorem 1.2.** For the same α_q and every η ∈ (0, 1) there are C > 0, n₀ and integers m_n with m_n / n → α_q
  such that, for n ≥ n₀, the hitting time H of non-q-colorability in the multigraph edge process satisfies
  |H − m_n| ≤ C n (log n)^{−3/2} with probability at least 1 − η.

Both are the single statement `ThresholdChallenge.MainStatement` in `Challenge.lean` (Mathlib only, 125 lines).
`Solution.lean` proves `ThresholdChallenge.main` with no `sorry` and with the axioms `propext`, `Quot.sound` and
`Classical.choice` only. The Comparator accepted it with con-ron `--verified`, NanoDa and Lean's default kernel on a
clean build (`verification/`).

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

`Challenge.lean` is the verbatim frozen 125-line headline challenge. The original
copy is also retained at `ThLean/Challenge/MainChallenge.lean`. Both have SHA-256
`037fe846ca2426d2d0f87527ce9618ce6a510099013691f8cd5c649093294856`.

`Solution.lean` imports the definitions-only companion through the project Bridge
and ends with:

```lean
theorem ThresholdChallenge.main : ThresholdChallenge.MainStatement := ThLean.Final.main
```

All 19 compiled companion declarations, including generated helpers, have exactly
the same names, universe parameters, types, and values as the frozen definitions.
The Solution's 547-module local import closure excludes the frozen theorem stub.
The permitted axioms are exactly `propext`, `Quot.sound`, and `Classical.choice`.
The definition-exemption list is empty.

Reproduce with the pinned Lean toolchain and dependency manifest:

```bash
lake exe cache get
lake build
python3 scripts/run_comparator.py --package . --report verification --label comparator
sha256sum -c verification/release-source.sha256
```

The runner exports the Challenge and Solution and invokes `lake comparator` with
its sandbox enabled. The requested kernels are `con-ron --verified`, NanoDa, and
Lean's default kernel (`leanchecker`). Success requires all three acceptance
markers and `Your solution is okay!`.

`verification/package-audit.json` records source hashes, dependency revisions,
the static import closure, and the compiler concurrency limit. The campaign's
`ThLean/FROZEN.sha256` remains a historical manifest: this release intentionally
changes the Bridge's import to the definitions-only companion. Use the release
source manifest above for this package.

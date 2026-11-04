# Statement and source fidelity

This audit compares the formal headline statement with Theorems 1.1 and 1.2 in
the included manuscript, and compares the ported Lean sources with release
commit `03a35c170b1135d8546c8d63ccadc7939389eff1`. No substantive statement mismatch
was found. The module port and added docstrings preserve every mathematical
token under the normalization recorded in `final-review/source-audit.json`.

## Manuscript correspondence

The included PDF and `paper/sections/01-intro.tex` (`thm:intro-main` and
`thm:intro-window`) give the same headline statements. In `Challenge.lean`:

- `MainStatement` quantifies every natural `q ≥ 3` and chooses **one** real
  threshold shared by `ThresholdStatement` and `WindowStatement`.
- The threshold lies in `[1/2, gamma q]`, where `gamma` is the manuscript's
  natural-log ratio. The four limits use fixed real densities: fixed-edge
  density `c` has threshold `α`, while sparse binomial density `d` has threshold
  `2α`. No conclusion is claimed at equality. The upper branches imply positive
  density from `α ≥ 1/2`.
- `completeEdges` contains unordered pairs of distinct vertices.
  `graphsWithEdges` selects all edge sets of exactly the requested size;
  `uniformColorabilityProbability` counts colorable sets and divides by the
  entire size class. `Colorable` requires an actual map to `Fin q` separating
  each edge's endpoints. Using `Fin n` rather than `[n]` only relabels vertices.
- `binomialColorabilityProbability` uses the independent-edge graph weight
  `p^|E| (1-p)^(n.choose 2 - |E|)`. The number of possible edges, rather than the
  number of vertices, appears in the absent-edge exponent.
- `sparseBinomialProbability` uses `p=d/n` on its valid domain and returns zero
  outside it. For fixed nonnegative `d`, this only changes finitely many initial
  terms. Likewise `Nat.floor (c*n)` equals the intended integer floor and lies
  within the possible-edge range eventually at fixed nonnegative `c`.
- `EdgePrefix` samples a sequence of independent uniform unordered pairs with
  replacement. Its denominator counts sequences, and `prefixMultigraph` retains
  repeated occurrences. Multiplicities do not change colorability.
- With `S_m = P(H>m)`, `hittingMass k = S_k-S_(k+1)` is the mass at `H=k+1`.
  `hittingWindowProbability` sums exactly the positive integer hitting times in
  `[a-w,a+w]`: it rounds after adding the real width to the center and retains
  the closed-interval endpoint conditions. An empty or negative-width window
  has probability zero; an infinite hitting time contributes no finite mass.
- `WindowStatement` uses every error probability in `(0,1)`, a positive real
  constant, integer centers converging after division by `n` to the same
  threshold, and the real exponent `-(3 : ℝ)/2`. Its onset bound
  `max 3 (2*q)` equals `2*q` for `q ≥ 3`, matching the manuscript. The onset
  keeps logarithms in the intended domain.

The scope is the two headline theorems. The challenge does not assert a numerical
threshold value, optimality of the window, or every supporting remark in the
manuscript. Four explanatory docstrings were added to `Colorable`,
`graphsWithEdges`, `MultigraphColorable`, and `gamma`, identically in the
definitions companion.

## Proof and model bridges reviewed

`ThLean/W/BR03/PublicModels.lean` proves model correspondence using explicit
pair/prefix equivalences, colorability transport, cardinality and finite-sum
reindexing, and normalization of Bernoulli graph weights.
`ThLean/W/BR05/WindowProbability.lean` transports survival probabilities and
proves the rounded interval identity with
`A=max 1 (ceil (a-w))`, `B=floor (a+w)`: the window is `S_(A-1)-S_B` when
`A ≤ B`, and zero otherwise. These correspondences are proved, not assumed.

`ThLean/Challenge/MainDefinitions.lean` is exactly the current Challenge source
with its final theorem and theorem docstring removed. The proof therefore uses
the same definitions as the statement file. `ThLean/BP/S4/Main.lean` constructs
the joint threshold/window witness from explicit internal results and the
public-model bridges. In `ThLean/Final/Main.lean`, the final assembly supplies
all nine antecedents of the section-composition contract and proves the closed
`ThresholdChallenge.MainStatement`; `Solution.lean` exposes that proof.

## Reproducible static checks

Run from the repository root:

```sh
python3 scripts/audit_submission.py
python3 scripts/check_finite_models.py
```

Both scripts use only Python's standard library. `final-review/source-audit.json` records
the baseline and current byte hashes, mathematical token hashes for all 444
Lean files, module headers, line caps, import graph, trust-marker scan, and
companion identity. The normalization ignores comments and whitespace outside
strings, the initial `module` command, `public` on imports, and the header
`@[expose] public section`. It retains all other tokens and exact string
contents. It found all mathematical token streams unchanged, all required
module headers present, no import cycles, and no unexpected trust markers.
The 442-file Solution closure excludes the deliberate Challenge theorem stub
and the unused aggregate `ThLean.lean`; it contains no `sorry`. All nonlocal
imports are Mathlib modules.

`finite-model-check.json` records exhaustive exact-rational checks on 282,123
length-seven edge sequences in two small models, 170 windows including
fractional and negative endpoints, and 10 Bernoulli/simple-model mixtures.
First-failure counts, survival differences, interval rounding, and graph-weight
normalization all agree. These checks exercise the generic finite formulas;
the small models are not instances of the asymptotic theorem's eventual domain.

## Scope of assurance

The source audit is lexical and static; it is not Lean's parser, a fresh build,
or kernel replay. Finite examples do not establish asymptotic conclusions.
This review covers the headline statement, probability definitions, selected
bridge proofs, and source/import integrity. It does not independently re-prove
every argument in the manuscript or constitute expert peer review of the whole
development. Fresh build and Comparator/kernel results for this edited tree
must be assessed separately; historical acceptance logs describe their original
source snapshot.

## Targeted literature check

A separate spot-check examined the introduction, related-work account, authors'
note, overview attribution, abstract, and bibliography. Primary-source checks
confirmed the sharp-threshold/convergence distinction in
[Achlioptas–Friedgut](https://cgi.di.uoa.gr/~optas/papers/k-col-threshold.pdf), the
log-probability limit and interpolation comparison in
[Bayati–Gamarnik–Tetali](https://arxiv.org/html/0912.2444v3), the cited bounds in
[Coja-Oghlan–Vilenchik](https://arxiv.org/html/1304.1063) and
[Ayre–Coja-Oghlan–Greenhill](https://arxiv.org/html/1812.09691v4), and the window
claims in Carenini's [TR26-229](https://eccc.weizmann.ac.il/report/2026/229/) and
[TR26-145](https://eccc.weizmann.ac.il/report/2026/145/). All four pinned OpenAI
preprint PDFs cited by the manuscript resolved; their main statements and
priority credit agree with the manuscript's summaries. The manuscript discloses
machine writing, the unrefereed status of recent preprints, and adapted proof
ingredients. No material attribution or literature discrepancy was found in this
scope. This check does not validate every one of the 63 bibliography entries or
independently establish the informal proofs.

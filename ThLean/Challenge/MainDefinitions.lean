module

public import Mathlib

@[expose] public section

/-!
The two headline statements of Aronow--Lopatto, frozen draft 2026-10-27.
This file has no project imports and no assumed section-level results.
All probabilities below are elementary counts or finite sums.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

namespace ThresholdChallenge

/-- Edges of the complete loopless graph on `Fin n`. -/
def completeEdges (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter (fun e => ∀ v : Fin n, e ≠ s(v, v))

/-- One unordered pair of distinct vertices. -/
abbrev Pair (n : ℕ) := {e : Sym2 (Fin n) // e ∈ completeEdges n}

/-- Existence of a vertex map to `Fin q` separating the endpoints of every edge in `E`. -/
def Colorable (q n : ℕ) (E : Finset (Sym2 (Fin n))) : Prop :=
  ∃ σ : Fin n → Fin q,
    ∀ u v : Fin n, s(u, v) ∈ E → σ u ≠ σ v

/-- All simple loopless graphs on `Fin n` with exactly `m` edges, represented by edge sets. -/
def graphsWithEdges (n m : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  (completeEdges n).powerset.filter (fun E => E.card = m)

/-- `P(G(n,m) is q-colorable)`, for `m ≤ n.choose 2`.
Outside this domain the empty denominator makes the total extension zero. -/
def uniformColorabilityProbability (q n m : ℕ) : ℝ :=
  (((graphsWithEdges n m).filter (Colorable q n)).card : ℝ) /
    ((graphsWithEdges n m).card : ℝ)

/-- `P(G(n,p) is q-colorable)`, for `0 ≤ p ≤ 1`.
The exponent uses the number of possible edges, not the number of vertices. -/
def binomialColorabilityProbability (q n : ℕ) (p : ℝ) : ℝ :=
  ∑ E ∈ (completeEdges n).powerset,
    p ^ E.card * (1 - p) ^ (n.choose 2 - E.card) *
      (if Colorable q n E then 1 else 0)

/-- The sparse binomial model. Its probability interpretation requires
`0 < n`, `0 ≤ d`, and `d ≤ n`. Invalid terms are set to zero;
for each fixed `d ≥ 0` there are only finitely many of them. -/
def sparseBinomialProbability (q n : ℕ) (d : ℝ) : ℝ :=
  if 0 < n ∧ 0 ≤ d ∧ d ≤ (n : ℝ) then
    binomialColorabilityProbability q n (d / (n : ℝ))
  else 0

/-- A uniform point of this finite type is exactly an iid uniform edge prefix. -/
abbrev EdgePrefix (n m : ℕ) := Fin m → Pair n

/-- The multiset retains repeated occurrences. -/
def prefixMultigraph {n m : ℕ} (x : EdgePrefix n m) : Multiset (Pair n) :=
  (List.ofFn x : Multiset (Pair n))

/-- Existence of a `q`-coloring separating the endpoints of every occurrence in `G`.
Repeated occurrences impose the same coloring constraint. -/
def MultigraphColorable (q : ℕ) {n : ℕ} (G : Multiset (Pair n)) : Prop :=
  ∃ σ : Fin n → Fin q,
    ∀ e ∈ G, ∀ u v : Fin n, e.val = s(u, v) → σ u ≠ σ v

/-- `S_m = P(G_m is colorable) = P(H > m)` for `q ≥ 1`, `n ≥ 2`.
The denominator counts sequences, not unordered multisets. -/
def processSurvival (q n m : ℕ) : ℝ :=
  (((Finset.univ : Finset (EdgePrefix n m)).filter
      (fun x => MultigraphColorable q (prefixMultigraph x))).card : ℝ) /
    (Fintype.card (EdgePrefix n m) : ℝ)

/-- `P(H=k+1)`. In particular `H=1` has mass `S_0-S_1`.
Under `q ≥ 1`, the empty graph is colorable and `H ≥ 1`. -/
def hittingMass (q n k : ℕ) : ℝ :=
  processSurvival q n k - processSurvival q n (k + 1)

/-- Probability of `|H-a| ≤ w`, with integer centre and real width.
Sum over `H=k+1`; `k < floor_nat(a+w)` means `k+1 ≤ a+w` whenever
the interval contains a positive integer. The indicator handles its lower end.
The sum is empty if `a+w < 1`; every summand is zero if `w < 0`.
`H=∞` contributes zero to every finite interval. For `n ≥ 2*q`, its
mass is zero (the lifetime bound in the paper); finiteness is not assumed
in this definition. No floor is applied to `w` before adding the centre. -/
def hittingWindowProbability (q n : ℕ) (a : ℤ) (w : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Nat.floor ((a : ℝ) + w)),
    if |((k + 1 : ℕ) : ℝ) - (a : ℝ)| ≤ w then hittingMass q n k else 0

/-- The first-moment upper bound on the threshold in edges per vertex:
`log q / log (q / (q - 1))`, with natural logarithms; used for `q ≥ 3`. -/
def gamma (q : ℕ) : ℝ :=
  Real.log (q : ℝ) / Real.log ((q : ℝ) / ((q : ℝ) - 1))

/-- Theorem 1.1, with the threshold supplied as an explicit argument.
For fixed `c ≥ 0`, `floor_nat(c*n)` agrees with the integer floor and is
at most `n.choose 2` eventually. No conclusion is asserted at equality. -/
def ThresholdStatement (q : ℕ) (α : ℝ) : Prop :=
  α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) ∧
  (∀ c : ℝ, 0 ≤ c → c < α →
    Tendsto (fun n : ℕ => uniformColorabilityProbability q n (Nat.floor (c * n)))
      atTop (𝓝 1)) ∧
  (∀ c : ℝ, α < c →
    Tendsto (fun n : ℕ => uniformColorabilityProbability q n (Nat.floor (c * n)))
      atTop (𝓝 0)) ∧
  (∀ d : ℝ, 0 ≤ d → d < 2 * α →
    Tendsto (fun n : ℕ => sparseBinomialProbability q n d) atTop (𝓝 1)) ∧
  (∀ d : ℝ, 2 * α < d →
    Tendsto (fun n : ℕ => sparseBinomialProbability q n d) atTop (𝓝 0))

/-- Theorem 1.2. The exponent is real `-3/2`, not natural subtraction.
Centres are integers, as in the paper. The onset includes the harmless
restrictions needed to interpret the logarithm and the edge process. -/
def WindowStatement (q : ℕ) (α : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, max 3 (2 * q) ≤ n₀ ∧
      ∃ a : ℕ → ℤ,
        Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) atTop (𝓝 α) ∧
        ∀ n : ℕ, n₀ ≤ n →
          1 - η ≤ hittingWindowProbability q n (a n)
            (C * (n : ℝ) * Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ) / 2))

/-- One existential forces the SAME threshold in Theorems 1.1 and 1.2.
This is the closed challenge, not a theorem assumed by the proofs. -/
def MainStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ α : ℝ, ThresholdStatement q α ∧ WindowStatement q α

end ThresholdChallenge

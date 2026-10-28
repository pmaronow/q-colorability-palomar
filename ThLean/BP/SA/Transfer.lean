import ThLean.BP.SA.Common
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.SA
open ThresholdFoundations

/-- Arbitrary event in the uniform fixed-size model. -/
def simpleEvent (n m : ℕ) (A : Finset (Sym2 (Fin n)) → Prop) : ℝ :=
  (((simpleGraphsWithEdges (V := Fin n) m).filter A).card : ℝ) /
    ((simpleGraphsWithEdges (V := Fin n) m).card : ℝ)
def distinctProbability (n m : ℕ) : ℝ :=
  uniformProb (fun x : EdgeTuple (Fin n) m => DistinctPrefix x)

/-- P5-X50, joint law on distinct samples; A:351,357--361. Paper label: `lem:conv-transfer`; blueprint: `P5-X50`. -/
def SA_X50aStatement : Prop :=
  ∀ n m : ℕ, 2 ≤ n → m ≤ n.choose 2 → ∀ A : Finset (Sym2 (Fin n)) → Prop,
    uniformProb (fun x : EdgeTuple (Fin n) m =>
      DistinctPrefix x ∧ A (edgeSupport (tupleGraph x))) =
    distinctProbability n m * simpleEvent n m A

/-- P5-X50, exact birthday product and positivity including zero samples. Paper label: `lem:conv-transfer`; blueprint: `P5-X50`. -/
def SA_X50bStatement : Prop :=
  ∀ n m : ℕ, 2 ≤ n → m ≤ n.choose 2 →
    distinctProbability n m =
      (∏ i ∈ Finset.range m, (1 - (i : ℝ) / (n.choose 2 : ℝ))) ∧
    0 < distinctProbability n m

/-- P5-X50; uniform law of a distinct prefix. Paper label: `lem:conv-transfer`; blueprint: `P5-X50`. -/
def SA_X50Statement : Prop := SA_X50aStatement ∧ SA_X50bStatement
theorem SA_X50_assembly (ha : SA_X50aStatement) (hb : SA_X50bStatement) :
    SA_X50Statement := ⟨ha, hb⟩

/-- P5-X51, finite birthday bound with all numerical hypotheses; A:351--355. Paper label: `lem:conv-transfer`; blueprint: `P5-X51`. -/
def SA_X51aStatement : Prop :=
  ∀ (Λ : ℝ) (n : ℕ), 0 ≤ Λ → 2 ≤ n →
    4 * Λ ≤ (n : ℝ) - 1 → 4 * Λ ^ 3 * n / ((n : ℝ) - 1) ^ 2 ≤ 1 →
    ∀ m : ℕ, (m : ℝ) ≤ Λ * n →
      m ≤ n.choose 2 ∧ Real.exp (-2 * Λ ^ 2 - 1) ≤ distinctProbability n m

/-- P5-X51, the finite birthday hypotheses eventually hold. Paper label: `lem:conv-transfer`; blueprint: `P5-X51`. -/
def SA_X51bStatement : Prop :=
  ∀ Λ : ℝ, 0 ≤ Λ → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    4 * Λ ≤ (n : ℝ) - 1 ∧ 4 * Λ ^ 3 * n / ((n : ℝ) - 1) ^ 2 ≤ 1

/-- P5-X51; finite and eventual birthday estimates. Paper label: `lem:conv-transfer`; blueprint: `P5-X51`. -/
def SA_X51Statement : Prop := SA_X51aStatement ∧ SA_X51bStatement
theorem SA_X51_assembly (ha : SA_X51aStatement) (hb : SA_X51bStatement) :
    SA_X51Statement := ⟨ha, hb⟩

/-- P5-X52, finite event comparison after the collision bound; A:357--361. Paper label: `lem:conv-transfer`; blueprint: `P5-X52`. -/
def SA_X52aStatement : Prop :=
  ∀ (q n m : ℕ) (Λ : ℝ), 1 ≤ q → 2 ≤ n → m ≤ n.choose 2 →
    Real.exp (-2 * Λ ^ 2 - 1) ≤ distinctProbability n m →
    1 - simpleProbability (V := Fin n) q m ≤
      Real.exp (2 * Λ ^ 2 + 1) * (1 - processSurvival (V := Fin n) q m) ∧
    simpleProbability (V := Fin n) q m ≤
      Real.exp (2 * Λ ^ 2 + 1) * processSurvival (V := Fin n) q m

/-- P5-X52; lem:conv-transfer(a), uniform in the whole linear range. Paper label: `lem:conv-transfer`; blueprint: `P5-X52`. -/
def SA_X52Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, 0 < Λ →
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ, (m : ℝ) ≤ Λ * n →
      m ≤ n.choose 2 ∧
      1 - simpleProbability (V := Fin n) q m ≤
        Real.exp (2 * Λ ^ 2 + 1) * (1 - processSurvival (V := Fin n) q m) ∧
      simpleProbability (V := Fin n) q m ≤
        Real.exp (2 * Λ ^ 2 + 1) * processSurvival (V := Fin n) q m

/-- P5-X53; monotonicity at valid fixed edge counts, A:340,363. Paper label: `lem:conv-transfer`; blueprint: `P5-X53`. -/
def SA_X53Statement : Prop :=
  ∀ q n m m' : ℕ, 1 ≤ q → 2 ≤ n → m ≤ m' → m' ≤ n.choose 2 →
    simpleProbability (V := Fin n) q m' ≤ simpleProbability (V := Fin n) q m

/-- P5-X54; finite binomial mixture including p=0 and p=1, A:363--365. Paper label: `lem:conv-transfer`; blueprint: `P5-X54`. -/
def SA_X54Statement : Prop :=
  ∀ q n : ℕ, 1 ≤ q → 2 ≤ n → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    bernoulliProbability (V := Fin n) q p =
      (∑ j ∈ Finset.range (n.choose 2 + 1),
        binomialWeight (n.choose 2) p j * simpleProbability (V := Fin n) q j) ∧
    (∀ j : ℕ, 0 ≤ binomialWeight (n.choose 2) p j) ∧
    (∑ j ∈ Finset.range (n.choose 2 + 1), binomialWeight (n.choose 2) p j) = 1

/-- P5-X55; lem:conv-transfer(b), strict and weak cutoff events kept distinct. Paper label: `lem:conv-transfer`; blueprint: `P5-X55`. -/
def SA_X55Statement : Prop :=
  ∀ q n m : ℕ, 1 ≤ q → 2 ≤ n → m ≤ n.choose 2 → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    simpleProbability (V := Fin n) q m * binomialEvent (n.choose 2) p (fun j => j ≤ m) ≤
      bernoulliProbability (V := Fin n) q p ∧
    bernoulliProbability (V := Fin n) q p ≤
      simpleProbability (V := Fin n) q m + binomialEvent (n.choose 2) p (fun j => j < m)

/-- P5-X56; binomial moments with real predecessor subtraction, A:400. Paper label: `lem:conv-transfer`; blueprint: `P5-X56`. -/
def SA_X56Statement : Prop :=
  ∀ B : ℕ, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    (∀ r : ℕ, Summable (fun k : ℕ => binomialWeight B p k * (k : ℝ) ^ r)) ∧
    (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ)) = (B : ℝ) * p ∧
    (∑ k ∈ Finset.range (B + 1),
      binomialWeight B p k * (k : ℝ) * ((k : ℝ) - 1)) = (B : ℝ) * ((B : ℝ) - 1) * p ^ 2 ∧
    (∑ k ∈ Finset.range (B + 1),
      binomialWeight B p k * ((k : ℝ) - (B : ℝ) * p) ^ 2) = (B : ℝ) * p * (1 - p) ∧
    (B : ℝ) * p * (1 - p) ≤ (B : ℝ) * p

/-- P5-X57; square-integrable Chebyshev, as used in A:400--408. Paper label: `lem:conv-transfer`; blueprint: `P5-X57`. -/
def SA_X57Statement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ), Measurable X → MemLp X 2 P → ∀ t : ℝ, 0 < t →
      P.real {ω | t ≤ |X ω - ∫ ω, X ω ∂P|} ≤
        (∫ ω, (X ω - ∫ ω', X ω' ∂P) ^ 2 ∂P) / t ^ 2

/-- P5-X58, quantitative upper/lower tails across a linear gap; A:400--408. Paper label: `lem:conv-transfer`; blueprint: `P5-X58`. -/
def SA_X58aStatement : Prop :=
  ∀ d : ℝ, 0 ≤ d →
    (∀ (c : ℝ) (n : ℕ), d / 2 < c → 2 ≤ n → d ≤ (n : ℝ) →
      binomialEvent (n.choose 2) (d / n) (fun k => Nat.floor (c * n) < k) ≤
        d / (2 * (c - d / 2) ^ 2 * n)) ∧
    (∀ (c : ℝ) (n : ℕ), 0 ≤ c → c < d / 2 → 2 ≤ n → d ≤ (n : ℝ) →
      d / (d / 2 - c) ≤ (n : ℝ) →
      binomialEvent (n.choose 2) (d / n) (fun k => k < Nat.floor (c * n)) ≤
        2 * d / ((d / 2 - c) ^ 2 * n))

/-- P5-X58, eventual vanishing of the two edge-count tails. Paper label: `lem:conv-transfer`; blueprint: `P5-X58`. -/
def SA_X58bStatement : Prop :=
  ∀ d : ℝ, 0 ≤ d →
    (∀ c : ℝ, d / 2 < c →
      Tendsto (fun n : ℕ => binomialEvent (n.choose 2) (d / n)
        (fun k => Nat.floor (c * n) < k)) atTop (𝓝 0)) ∧
    (∀ c : ℝ, 0 ≤ c → c < d / 2 →
      Tendsto (fun n : ℕ => binomialEvent (n.choose 2) (d / n)
        (fun k => k < Nat.floor (c * n))) atTop (𝓝 0))

/-- P5-X58; finite and asymptotic binomial edge-count tails. Paper label: `lem:conv-transfer`; blueprint: `P5-X58`. -/
def SA_X58Statement : Prop := SA_X58aStatement ∧ SA_X58bStatement
theorem SA_X58_assembly (ha : SA_X58aStatement) (hb : SA_X58bStatement) :
    SA_X58Statement := ⟨ha, hb⟩

/-- P5-X52 assembly from the birthday cutoff and finite comparison. -/
theorem SA_X52_assembly (h51 : SA_X51Statement) (h52 : SA_X52aStatement) :
    SA_X52Statement := by
  intro q hq Λ hΛ
  obtain ⟨N, hN, hlarge⟩ := h51.2 Λ hΛ.le
  refine ⟨N, hN, ?_⟩
  intro n hn m hm
  obtain ⟨hc₁, hc₂⟩ := hlarge n hn
  obtain ⟨hvalid, hprob⟩ := h51.1 Λ n hΛ.le (le_trans hN hn) hc₁ hc₂ m hm
  exact ⟨hvalid, h52 q n m Λ (by omega) (le_trans hN hn) hvalid hprob⟩

/-- Cutoff sums used by the frozen binomial-transfer interface, P5-X55. Paper label: `lem:conv-transfer`; blueprint: `P5-X55`. -/
def SA_X55aStatement : Prop :=
  ∀ B m : ℕ, m ≤ B → ∀ p : ℝ,
    binomialEvent B p (fun j => j ≤ m) =
      (∑ j ∈ Finset.range (m + 1), binomialWeight B p j) ∧
    binomialEvent B p (fun j => j < m) =
      (∑ j ∈ Finset.range m, binomialWeight B p j)

/-- Eventual uniform-model domain and agreement of natural and integer floors. Paper label: `thm:red-convergence`; blueprint: `P5-C64`. -/
def SA_X59aStatement : Prop :=
  ∀ c : ℝ, 0 ≤ c → ∀ᶠ n : ℕ in atTop,
    Nat.floor (c * n) ≤ n.choose 2 ∧ (Nat.floor (c * n) : ℤ) = Int.floor (c * n)

/-- Eventual domain for a fixed sparse-binomial density, P5-C65 / B21. Paper label: `thm:red-convergence`; blueprint: `P5-C65`. -/
def SA_X59bStatement : Prop :=
  ∀ d : ℝ, 0 ≤ d → ∀ᶠ n : ℕ in atTop, 0 < n ∧ d ≤ (n : ℝ)

/-- P5-X50, colorability specialization of the joint support law, B19. Paper label: `lem:conv-transfer`; blueprint: `P5-X50`. -/
def SA_X50cStatement : Prop :=
  ∀ q n m : ℕ, 1 ≤ q → 2 ≤ n → m ≤ n.choose 2 →
    uniformProb (fun x : EdgeTuple (Fin n) m =>
      DistinctPrefix x ∧ Colorable q (tupleGraph x)) =
      distinctProbability n m * simpleProbability (V := Fin n) q m
end ThLean.BP.SA

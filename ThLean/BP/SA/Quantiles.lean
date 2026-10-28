import ThLean.BP.SA.Interpolation
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.SA
open ThresholdFoundations

/-- P5-Q24: a cutoff fixed before any interpolation density is selected. -/
def GoodCutoff (q : ℕ) (Λ η : ℝ) (n₁ s₀ : ℕ) : Prop :=
  max (max (2 * q) n₁) (Nat.ceil (Real.exp 2)) ≤ s₀ ∧
  ∀ n : ℕ, s₀ ≤ n → upperLocation q Λ η n < cap Λ n ∧
    (1 / 4 : ℝ) < xi q Λ η n ∧
    2 * (poissonDeviation n : ℝ) / n < (1 / 4 : ℝ) ∧
    poissonTailError Λ n ≤ min η (1 / 8 : ℝ)

/-- P5-Q20; lem:conv-quantile(a), eq:conv-rho-H. Paper label: `lem:conv-quantile`; blueprint: `P5-Q20`. -/
def SA_Q20Statement : Prop :=
  ∀ q n : ℕ, 1 ≤ q → 2 ≤ n → ∀ c : ℝ, 0 ≤ c →
    Summable (fun j : ℕ => poissonWeight (c * ((n : ℝ) - 1)) j *
      processSurvival (V := Fin n) q j) ∧
    0 ≤ poissonMixture (c * ((n : ℝ) - 1)) (processSurvival (V := Fin n) q) ∧
    poissonMixture (c * ((n : ℝ) - 1)) (processSurvival (V := Fin n) q) ≤ 1 ∧
    rho q n c = Real.exp (-c) *
      poissonMixture (c * ((n : ℝ) - 1)) (processSurvival (V := Fin n) q)

/-- P5-Q22, lower smoothing bound; eq:conv-below. Paper label: `lem:conv-quantile`; blueprint: `P5-Q22`. -/
def SA_Q22aStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2 * q ≤ n →
    ∀ Λ η c : ℝ, gamma q + 1 < Λ → 0 < η → η ≤ 1 / 2 → 0 < c → c ≤ Λ →
    c * ((n : ℝ) - 1) ≤ (lowerLocation q Λ η n : ℝ) - poissonDeviation n →
    Real.exp (-Λ) * (1 - η) * (1 - poissonTailError Λ n) ≤ rho q n c

/-- P5-Q22, upper smoothing bound with its indispensable cap condition. Paper label: `lem:conv-quantile`; blueprint: `P5-Q22`. -/
def SA_Q22bStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2 * q ≤ n →
    ∀ Λ η c : ℝ, gamma q + 1 < Λ → 0 < η → η ≤ 1 / 2 →
    0 < c → c ≤ Λ → upperLocation q Λ η n < cap Λ n →
    (upperLocation q Λ η n : ℝ) + poissonDeviation n ≤ c * ((n : ℝ) - 1) →
    rho q n c ≤ η + poissonTailError Λ n

/-- P5-Q22; both quantitative smoothing implications. Paper label: `lem:conv-quantile`; blueprint: `P5-Q22`. -/
def SA_Q22Statement : Prop := SA_Q22aStatement ∧ SA_Q22bStatement

theorem SA_Q22_assembly (ha : SA_Q22aStatement) (hb : SA_Q22bStatement) :
    SA_Q22Statement := ⟨ha, hb⟩

/-- P5-Q23, real calculus for the monotone envelope; A:165--169. Paper label: `lem:conv-superadd`; blueprint: `P5-Q23`. -/
def SA_Q23aStatement : Prop :=
  (∀ u : ℝ, Real.exp 2 ≤ u → 0 ≤ envelope u ∧ 0 ≤ envelope u + 1 / u) ∧
  AntitoneOn envelope (Set.Ici (Real.exp 2)) ∧
  AntitoneOn (fun u : ℝ => envelope u + 1 / u) (Set.Ici (Real.exp 2)) ∧
  Tendsto envelope atTop (𝓝 0) ∧
  Tendsto (fun u : ℝ => envelope u + 1 / u) atTop (𝓝 0) ∧
  ∀ u : ℝ, Real.exp 1 ≤ u → 1 / u ≤ envelope u

/-- P5-Q23, ceiling and Poisson error estimates; eq:conv-Delta-bound. Paper label: `lem:conv-superadd`; blueprint: `P5-Q23`. -/
def SA_Q23bStatement : Prop :=
  (∀ n : ℕ, 1 ≤ n → 0 ≤ (poissonDeviation n : ℝ) / n ∧
    (poissonDeviation n : ℝ) / n ≤ envelope n + 1 / (n : ℝ)) ∧
  (∀ Λ : ℝ, 0 < Λ → Tendsto (poissonTailError Λ) atTop (𝓝 0))

/-- P5-Q23, geometric-scale envelope series; A:374--376. Paper label: `lem:conv-superadd`; blueprint: `P5-Q23`. -/
def SA_Q23cStatement : Prop :=
  Summable (fun k : ℕ => (k + 1 : ℝ) * Real.exp (-(k + 1 : ℝ) / 2))

/-- P5-Q23; all envelope estimates. Paper label: `lem:conv-superadd`; blueprint: `P5-Q23`. -/
def SA_Q23Statement : Prop := SA_Q23aStatement ∧ SA_Q23bStatement ∧ SA_Q23cStatement

theorem SA_Q23_assembly (ha : SA_Q23aStatement) (hb : SA_Q23bStatement)
    (hc : SA_Q23cStatement) : SA_Q23Statement := ⟨ha, hb, hc⟩

/-- P5-Q24; one common large-size cutoff, eq:conv-s0. Paper label: `lem:conv-superadd`; blueprint: `P5-Q24`. -/
def SA_Q24Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ η : ℝ, gamma q + 1 < Λ →
    0 < η → η ≤ etaZero Λ → ∀ n₁ : ℕ, ∃ s₀ : ℕ, GoodCutoff q Λ η n₁ s₀

/-- P5-Q25; inversion of large Poisson survival, A:191--202. Paper label: `lem:conv-superadd`; blueprint: `P5-Q25`. -/
def SA_Q25Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2 * q ≤ n →
    ∀ (Λ η K c : ℝ) (δ : ℕ → ℝ) (n₁ : ℕ),
    gamma q + 1 < Λ → AdmissibleError δ → 0 < η → η ≤ etaZero Λ →
    WindowAt q Λ δ η K n₁ → n₁ ≤ n → 0 < c → c ≤ Λ →
    upperLocation q Λ η n < cap Λ n → poissonTailError Λ n ≤ η →
    Real.exp (-2 * Λ) / 2 < rho q n c →
      c * ((n : ℝ) - 1) < (upperLocation q Λ η n : ℝ) + poissonDeviation n ∧
      c - Λ / n - K * δ n - (poissonDeviation n : ℝ) / n < xi q Λ η n

/-- P5-Q26; comparison of two large blocks, A:174--212. Paper label: `lem:conv-superadd`; blueprint: `P5-Q26`. -/
def SA_Q26Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (Λ η K : ℝ) (δ : ℕ → ℝ) (n₁ s₀ : ℕ),
    gamma q + 1 < Λ → AdmissibleError δ → 0 < η → η ≤ etaZero Λ →
    WindowAt q Λ δ η K n₁ → GoodCutoff q Λ η n₁ s₀ →
    ∀ a b : ℕ, s₀ ≤ a → s₀ ≤ b →
      min (xi q Λ η a) (xi q Λ η b) - comparisonError δ Λ K (min a b : ℕ) ≤
        xi q Λ η (a + b)

/-- P5-Q27; adjacent sizes using the one-vertex model, A:214--223. Paper label: `lem:conv-superadd`; blueprint: `P5-Q27`. -/
def SA_Q27Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (Λ η K : ℝ) (δ : ℕ → ℝ) (n₁ s₀ : ℕ),
    gamma q + 1 < Λ → AdmissibleError δ → 0 < η → η ≤ etaZero Λ →
    WindowAt q Λ δ η K n₁ → GoodCutoff q Λ η n₁ s₀ →
    ∀ a : ℕ, s₀ ≤ a → xi q Λ η a - comparisonError δ Λ K a ≤ xi q Λ η (a + 1)

/-- P5-Q28; lem:conv-superadd. Paper label: `lem:conv-superadd`; blueprint: `P5-Q28`. -/
def SA_Q28Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (Λ η K : ℝ) (δ : ℕ → ℝ) (n₁ : ℕ),
    gamma q + 1 < Λ → AdmissibleError δ → 0 < η → η ≤ etaZero Λ →
    WindowAt q Λ δ η K n₁ →
    ∃ s₀ : ℕ, 2 * q ≤ s₀ ∧ Compares (xi q Λ η) (comparisonError δ Λ K) s₀

theorem SA_Q28_assembly (h24 : SA_Q24Statement) (h26 : SA_Q26Statement)
    (h27 : SA_Q27Statement) : SA_Q28Statement := by
  intro q hq Λ η K δ n₁ hΛ hδ hη hη₀ hw
  obtain ⟨s₀, hs₀⟩ := h24 q hq Λ η hΛ hη hη₀ n₁
  have hqs : 2 * q ≤ s₀ :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs₀.1
  refine ⟨s₀, hqs, ?_, ?_, ?_⟩
  · omega
  · intro a b ha hb
    simpa only [Nat.cast_min] using h26 q hq Λ η K δ n₁ s₀ hΛ hδ hη hη₀ hw hs₀ a b ha hb
  · exact h27 q hq Λ η K δ n₁ s₀ hΛ hδ hη hη₀ hw hs₀
end ThLean.BP.SA

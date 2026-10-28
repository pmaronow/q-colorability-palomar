import ThLean.BP.SA.Interpolation
import ThLean.BP.SA.Transfer
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.SA
open ThresholdFoundations

/-- Global ordered-pair insertion operator of P5-R70. -/
def globalStep (n₁ n₂ : ℕ) (f : MGraph (Fin (n₁ + n₂)) → ℝ)
    (G : MGraph (Fin (n₁ + n₂))) : ℝ :=
  uniformMean (fun xy : Fin (n₁ + n₂) × Fin (n₁ + n₂) => f (addEdge G s(xy.1, xy.2)))

/-- Local size-weighted ordered-pair insertion operator of P5-R70. -/
def localStep (n₁ n₂ : ℕ) (f : MGraph (Fin (n₁ + n₂)) → ℝ)
    (G : MGraph (Fin (n₁ + n₂))) : ℝ :=
  (n₁ : ℝ) / ((n₁ + n₂ : ℕ) : ℝ) *
    uniformMean (fun xy : Fin n₁ × Fin n₁ =>
      f (addEdge G s(leftVertex n₁ n₂ xy.1, leftVertex n₁ n₂ xy.2))) +
  (n₂ : ℝ) / ((n₁ + n₂ : ℕ) : ℝ) *
    uniformMean (fun xy : Fin n₂ × Fin n₂ =>
      f (addEdge G s(rightVertex n₁ n₂ xy.1, rightVertex n₁ n₂ xy.2)))

/-- P5-R70, commuting-operator comparison, alternative to A:57--96. Paper label: `lem:conv-interp`; blueprint: `P5-R70`. -/
def SA_R70aStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ m : ℕ,
    ∀ G : MGraph (Fin (n₁ + n₂)),
      ((localStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) G ≤
      ((globalStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) G

/-- P5-R70, the two Poisson mixtures of the insertion iterates. Paper label: `lem:conv-interp`; blueprint: `P5-R70`. -/
def SA_R70bStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ c : ℝ, 0 ≤ c →
    (∀ m : ℕ, 0 ≤ poissonWeight (c * (n₁ + n₂ : ℕ)) m) ∧
    Summable (fun m : ℕ => poissonWeight (c * (n₁ + n₂ : ℕ)) m *
      ((globalStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0) ∧
    Summable (fun m : ℕ => poissonWeight (c * (n₁ + n₂ : ℕ)) m *
      ((localStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0) ∧
    poissonMixture (c * (n₁ + n₂ : ℕ))
      (fun m => ((globalStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0) =
      rho q (n₁ + n₂) c ∧
    poissonMixture (c * (n₁ + n₂ : ℕ))
      (fun m => ((localStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0) =
      rho q n₁ c * rho q n₂ c

/-- P5-R70; finite comparison and its product-inequality consequence. Paper label: `lem:conv-interp`; blueprint: `P5-R70`. -/
def SA_R70Statement : Prop := SA_R70aStatement ∧ SA_I17Statement

/-- P5-R71; Chebyshev alternative to the exponential quantile smoothing constants. Paper label: `lem:conv-quantile`; blueprint: `P5-R71`. -/
def SA_R71Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2 * q ≤ n → ∀ Λ η c : ℝ,
    gamma q + 1 < Λ → 0 < η → η ≤ 1 / 2 → 0 < c → c ≤ Λ →
    (c * ((n : ℝ) - 1) ≤ (lowerLocation q Λ η n : ℝ) - poissonDeviation n →
      Real.exp (-Λ) * (1 - η) * (1 - Λ / (Real.log (n : ℝ)) ^ 2) ≤ rho q n c) ∧
    (upperLocation q Λ η n < cap Λ n →
      (upperLocation q Λ η n : ℝ) + poissonDeviation n ≤ c * ((n : ℝ) - 1) →
      rho q n c ≤ η + Λ / (Real.log (n : ℝ)) ^ 2)

/-- P5-E01b; discrete square-integrability and Poisson moment identities. Paper label: `lem:conv-quantile`; blueprint: `P5-E01b`. -/
def SA_E01bStatement : Prop :=
  ∀ μ : ℝ, 0 ≤ μ →
    Summable (fun j : ℕ => poissonWeight μ j * (j : ℝ)) ∧
    Summable (fun j : ℕ => poissonWeight μ j * (j : ℝ) ^ 2) ∧
    (∑' j : ℕ, poissonWeight μ j * (j : ℝ)) = μ ∧
    (∑' j : ℕ, poissonWeight μ j * (j : ℝ) * ((j : ℝ) - 1)) = μ ^ 2 ∧
    (∑' j : ℕ, poissonWeight μ j * (j : ℝ) ^ 2) = μ ^ 2 + μ ∧
    (∑' j : ℕ, poissonWeight μ j * ((j : ℝ) - μ) ^ 2) = μ

theorem SA_R70_assembly (ha : SA_R70aStatement) (hb : SA_R70bStatement) :
    SA_R70Statement := by
  refine ⟨ha, ?_⟩
  intro q n₁ n₂ hq h₁ h₂ c hc
  obtain ⟨hw, hsumG, hsumL, hG, hL⟩ := hb q n₁ n₂ hq h₁ h₂ c hc
  rw [← hG, ← hL]
  exact Summable.tsum_le_tsum
    (fun m => mul_le_mul_of_nonneg_left (ha q n₁ n₂ hq h₁ h₂ m 0) (hw m)) hsumL hsumG
end ThLean.BP.SA

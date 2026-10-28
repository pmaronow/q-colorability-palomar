import ThLean.BP.SA.Interpolation
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ThLean.BP.SA
open ThresholdFoundations

/-- Factorial majorant for derivatives on the cube of radius R. -/
def poissonMajorant (R : ℝ) (r : ℕ) (k : Fin 3 → ℕ) : ℝ :=
  ∏ i : Fin 3, ((k i + 1 : ℕ) : ℝ) ^ r * (R + 1) ^ k i / (Nat.factorial (k i) : ℝ)

/-- B18 supplement to P5-I13: derivative bounds for each factorial-series term. Paper label: `lem:conv-interp`; blueprint: `P5-I13`. -/
def SA_I13eStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ R : ℝ, 0 ≤ R → ∀ r : ℕ,
    ∃ C : ℝ, 0 < C ∧ ∀ (k : Fin 3 → ℕ) (μ : Fin 3 → ℝ),
      (∀ i, |μ i| ≤ R) →
      ‖iteratedFDeriv ℝ r (interpolationTerm q n₁ n₂ k) μ‖ ≤ C * poissonMajorant R r k

/-- B18 supplement to P5-I13: factorial majorants are summable. Paper label: `lem:conv-interp`; blueprint: `P5-I13`. -/
def SA_I13fStatement : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ r : ℕ, Summable (poissonMajorant R r)

/-- B18 supplement to P5-I13: absolute, locally uniform derivative convergence. Paper label: `lem:conv-interp`; blueprint: `P5-I13`. -/
def SA_I13gStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ r : ℕ,
    (∀ μ : Fin 3 → ℝ, Summable (fun k : Fin 3 → ℕ =>
      ‖iteratedFDeriv ℝ r (interpolationTerm q n₁ n₂ k) μ‖)) ∧
    TendstoLocallyUniformly (interpolationDerivativeNormPartial q n₁ n₂ r)
      (fun μ => ∑' k : Fin 3 → ℕ, ‖iteratedFDeriv ℝ r (interpolationTerm q n₁ n₂ k) μ‖) atTop
end ThLean.BP.SA

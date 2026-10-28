import ThLean.BP.S5.Occupation

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.S541
open ThresholdFoundations ThLean.BP.S5

/-- Root splitting and the frozen-list obstruction reduce the root event to
short random-list obstructions. -/
def S5_32RootPoissonReductionStatement : Prop :=
  ∀ (_h03 : ThLean.BP.S5.S5_03Statement)
    (_h09B : ThLean.BP.S5.S5_09BStatement)
    (_hRelabel : ThresholdFoundations.PreRelabelStatement.{0, 0})
    (_hE01 : ThLean.BP.S5.S5_E01Statement)
    (_hE08 : ThLean.BP.S5.S5_E08Statement),
  ∀ q n D : ℕ, 3 ≤ q → 3 ≤ n → ∀ a : Fin n, ∀ t : ℝ, 0 ≤ t →
    rootProbability q D a t ≤
      (∑ j ∈ Finset.range (D + 1), poissonWeight (2 * t / n) j *
        nmTime q (n - 1) j ((((n : ℝ) - 2) / n) * t))

/-- Prefix monotonicity and Poisson mass contraction bound the truncated
mixture by the length-D random-list obstruction. -/
def S5_32PoissonWeightContractionStatement : Prop :=
  ∀ (_h06 : ThLean.BP.S5.S5_06Statement)
    (_hE01 : ThLean.BP.S5.S5_E01Statement),
  ∀ q n D : ℕ, 3 ≤ q → 3 ≤ n → ∀ t : ℝ, 0 ≤ t →
    (∑ j ∈ Finset.range (D + 1), poissonWeight (2 * t / n) j *
      nmTime q (n - 1) j ((((n : ℝ) - 2) / n) * t)) ≤
        nmTime q (n - 1) D ((((n : ℝ) - 2) / n) * t)

end ThLean.Contrib.S541

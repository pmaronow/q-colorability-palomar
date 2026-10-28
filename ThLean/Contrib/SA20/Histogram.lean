import ThLean.BP.SA.Interpolation

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.SA20
open ThresholdFoundations

/-- Weighted counts of ordered mark sequences with a fixed histogram equal
the multinomial coefficient times the product of mark weights. -/
def CountHistogramStatement : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D]
    (ν : D → ℝ) (k : ℕ) (z : D → ℕ),
    (∑ x : Fin k → D,
      (∏ i, ν (x i)) * indicator (∀ e, (List.ofFn x).count e = z e)) =
      if (∑ e, z e) = k then
        ((Nat.factorial k : ℝ) / ∏ e, (Nat.factorial (z e) : ℝ)) *
          ∏ e, ν e ^ z e
      else 0

/-- Signed algebraic factorization of the Poisson weight after the histogram
coefficient has been identified. -/
def PoissonProductFactorStatement : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D]
    (ν : D → ℝ) (μ : ℝ) (z : D → ℕ),
    (∑ e, ν e) = 1 →
    poissonWeight μ (∑ e, z e) *
      (((Nat.factorial (∑ e, z e) : ℝ) /
          ∏ e, (Nat.factorial (z e) : ℝ)) * ∏ e, ν e ^ z e) =
      ∏ e, poissonWeight (μ * ν e) (z e)

end ThLean.Contrib.SA20

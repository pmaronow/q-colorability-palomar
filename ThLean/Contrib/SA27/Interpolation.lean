import ThLean.BP.SA.Interpolation

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.SA27
open ThresholdFoundations ThLean.BP.SA

/-- The remaining marked-count expansion in the frozen interpolation bridge.
Given support invariance and the signed marked-Poisson count factorization,
the frozen factorial series is the series over counts of the individual
tagged endpoint marks. -/
def MarkedInterpolationExpansionStatement
    (_h10 : SA_I10Statement) (_h11a : SA_I11aStatement) : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ μ : Fin 3 → ℝ,
    chiBar q n₁ n₂ μ =
      ∑' z : InterpolationMark n₁ n₂ → ℕ,
        (∏ e : InterpolationMark n₁ n₂,
          poissonWeight (interpolationMarkRate μ e) (z e)) *
          indicator (Colorable q (supportGraph interpolationMarkEdge
            (Finset.univ.filter (fun e => 0 < z e))))

end ThLean.Contrib.SA27

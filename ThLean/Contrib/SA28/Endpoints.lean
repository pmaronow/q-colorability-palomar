import ThLean.BP.SA.Common

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.SA28
open ThresholdFoundations
open ThLean.BP.SA

/-- The two interpolation endpoint identifications with the Poisson colorability laws. -/
def SA_I13bEndpointsStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ c : ℝ, 0 ≤ c →
    finiteChi q n₁ n₂ c 0 = rho q n₁ c * rho q n₂ c ∧
    finiteChi q n₁ n₂ c c = rho q (n₁ + n₂) c

end ThLean.Contrib.SA28

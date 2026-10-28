import ThLean.BP.SA.Alternatives

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.SA51
open ThresholdFoundations ThLean.BP.SA

/-- Remaining global endpoint-sampling law for the SA-R70b leaf. -/
def GlobalPoissonMixtureIdentityStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ c : ℝ, 0 ≤ c →
    poissonMixture (c * (n₁+n₂ : ℕ))
      (fun m => ((globalStep n₁ n₂)^[m])
        (fun H => indicator (Colorable q H)) 0) = rho q (n₁+n₂) c

/-- Remaining local thinning and component-factorization law for SA-R70b. -/
def LocalPoissonMixtureIdentityStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ c : ℝ, 0 ≤ c →
    poissonMixture (c * (n₁+n₂ : ℕ))
      (fun m => ((localStep n₁ n₂)^[m])
        (fun H => indicator (Colorable q H)) 0) = rho q n₁ c * rho q n₂ c

end ThLean.Contrib.SA51

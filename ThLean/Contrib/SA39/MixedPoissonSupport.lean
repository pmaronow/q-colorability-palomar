import ThLean.BP.SA.Common

noncomputable section
open scoped BigOperators

namespace ThLean.Contrib.SA39
open ThresholdFoundations
open ThLean.BP.SA

/-- Poissonization of the three independently sampled finite mark lists can be
reorganized by the set of marks that occur. The support invariance hypothesis
is what lets multiplicities be erased before taking the expectation. -/
def MixedMarkSupportStatement : Prop :=
  ∀ (n₁ n₂ : ℕ) (μ : Fin 3 → ℝ)
    (h : MGraph (Fin (n₁ + n₂)) → ℝ),
    (∀ G G', edgeSupport G = edgeSupport G' → h G = h G') →
      Summable (fun k : Fin 3 → ℕ =>
        (∏ i : Fin 3, poissonWeight (μ i) (k i)) *
          mixedGraphMean n₁ n₂ k h) ∧
      poissonInterpolationMean n₁ n₂ μ h =
        supportMean (fun T => h (supportGraph T)) (markRate n₁ n₂ μ)

end ThLean.Contrib.SA39

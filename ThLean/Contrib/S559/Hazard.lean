import ThLean.BP.S5.Poisson

noncomputable section
open scoped BigOperators Topology ENNReal

namespace ThLean.Contrib.S559
open ThresholdFoundations ThLean.BP.S5

/-- Poisson mixing of normalized root increments gives the mean frozen-pair
hazard under the augmented graph law. -/
def S5_15BHazardStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
  ∀ rate s : ℝ, 0 < rate → 0 ≤ s →
    poissonMixture (rate * Fintype.card V * s)
      (incrementMean (V := V) q (rate * s)) =
    poissonGraphMean (V := Option V)
      (rate * ((Fintype.card V + 1).choose 2 : ℝ) * s) (kappa q)

end ThLean.Contrib.S559

import ThLean.BP.SA.Quantiles

noncomputable section
open scoped BigOperators
namespace ThLean.Contrib.SA40
open ThresholdFoundations

/-- The model-specific loop-splitting identity required by P5-Q20. -/
def Q20LoopSplitBridgeStatement : Prop :=
  ∀ q n : ℕ, 1 ≤ q → 2 ≤ n → ∀ c : ℝ, 0 ≤ c →
    rho q n c = Real.exp (-c) *
      poissonMixture (c * ((n : ℝ) - 1)) (processSurvival (V := Fin n) q)

/-- Every finite edge-process survival probability lies in the unit interval. -/
def Q20ProcessSurvivalUnitIntervalStatement : Prop :=
  ∀ q n : ℕ, 1 ≤ q → 2 ≤ n → ∀ j : ℕ,
    0 ≤ processSurvival (V := Fin n) q j ∧
      processSurvival (V := Fin n) q j ≤ 1

end ThLean.Contrib.SA40

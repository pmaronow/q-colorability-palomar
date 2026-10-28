import ThLean.BP.SA.Convergence

noncomputable section

namespace ThLean.W.SA11

open Filter
open scoped Topology

/-- The two one-sided limits at distinct thresholds contradict uniqueness of limits. -/
theorem SA_C67Statement_holds : ThLean.BP.SA.SA_C67Statement := by
  intro q hq α β hα hβ hαlim hβlim
  by_contra hne
  rcases lt_or_gt_of_ne hne with hαβ | hβα
  · let c : ℝ := (α + β) / 2
    have hc0 : 0 ≤ c := by
      dsimp [c]
      positivity
    have hαc : α < c := by
      dsimp [c]
      linarith
    have hcβ : c < β := by
      dsimp [c]
      linarith
    have htoOne : Tendsto
        (fun n : ℕ => ThresholdFoundations.processSurvival (V := Fin n) q
          (Nat.floor (c * n))) atTop (𝓝 1) := hβlim.1 c hc0 hcβ
    have htoZero : Tendsto
        (fun n : ℕ => ThresholdFoundations.processSurvival (V := Fin n) q
          (Nat.floor (c * n))) atTop (𝓝 0) := hαlim.2 c hαc
    have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique htoOne htoZero
    exact one_ne_zero h10
  · let c : ℝ := (α + β) / 2
    have hc0 : 0 ≤ c := by
      dsimp [c]
      positivity
    have hβc : β < c := by
      dsimp [c]
      linarith
    have hcα : c < α := by
      dsimp [c]
      linarith
    have htoOne : Tendsto
        (fun n : ℕ => ThresholdFoundations.processSurvival (V := Fin n) q
          (Nat.floor (c * n))) atTop (𝓝 1) := hαlim.1 c hc0 hcα
    have htoZero : Tendsto
        (fun n : ℕ => ThresholdFoundations.processSurvival (V := Fin n) q
          (Nat.floor (c * n))) atTop (𝓝 0) := hβlim.2 c hβc
    have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique htoOne htoZero
    exact one_ne_zero h10

example : ThLean.BP.SA.SA_C67Statement := SA_C67Statement_holds

end ThLean.W.SA11

import ThLean.BP.S3.Adapters

noncomputable section
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S384
open ThresholdFoundations
universe u

theorem S3_16bStatement_of_deps
    (h16 : ThLean.BP.S3.S3_16Statement.{u}) :
    ThLean.BP.S3.S3_16bStatement.{u} := by
  classical
  intro V _ q hq hV
  constructor
  · intro J h hh
    let z : (m : ℕ) → EdgeTuple V m → ℝ := fun m x => h m (tupleGraph x)
    have hz : ∀ m ∈ (J : Set ℕ), ∀ x, 0 ≤ z m x ∧ z m x ≤ 1 := by
      intro m hm x
      exact hh m hm (tupleGraph x)
    let a : ℕ → ℝ := fun m =>
      if m ∈ (J : Set ℕ) then
        uniformMean (fun x : EdgeTuple V m => z m x * kappa q (tupleGraph x))
      else 0
    have hsum := h16 V q hq hV (J : Set ℕ) z hz
    rcases hsum with ⟨ha, hineq, htail, htotal⟩
    have hleft :
        (∑ m ∈ J, graphMean m (fun G => h m G * kappa q G)) = ∑' m, a m := by
      rw [sum_eq_tsum_indicator]
      simp [a, z, graphMean, Set.indicator]
    have hright :
        (∑ m ∈ J, hittingMass (V := V) q m) =
          ∑' m, if m ∈ (J : Set ℕ) then hittingMass (V := V) q m else 0 := by
      rw [sum_eq_tsum_indicator]
      simp [Set.indicator]
    rw [hleft, hright]
    simpa [a] using hineq
  · intro J
    have hz : ∀ m ∈ (J : Set ℕ), ∀ x : EdgeTuple V m, 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := by
      intro m hm x
      exact ⟨le_rfl, by norm_num⟩
    have hsum := h16 V q hq hV (J : Set ℕ) (fun _ _ => 0) hz
    have hright :
        (∑ m ∈ J, hittingMass (V := V) q m) =
          ∑' m, if m ∈ (J : Set ℕ) then hittingMass (V := V) q m else 0 := by
      rw [sum_eq_tsum_indicator]
      simp [Set.indicator]
    rw [hright]
    convert hsum.2.2.1 using 1
    apply tsum_congr
    intro m
    by_cases hm : m ∈ J <;> simp [hm]

end ThLean.W.S384

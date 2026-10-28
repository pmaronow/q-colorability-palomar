import ThLean.BP.S5.Elementary

noncomputable section
open scoped BigOperators ENNReal

namespace ThLean.W.S510
open ThresholdFoundations

private theorem poissonTail_real_tsum
    (hE01 : ThLean.BP.S5.S5_E01Statement)
    (z : ℝ) (hz : 0 ≤ z) (i : ℕ) :
    poissonTail z (i : ℝ) =
      ∑' j : ℕ, if i ≤ j then poissonWeight z j else 0 := by
  have hmass := hE01.1 z hz
  have hweight_nonneg : ∀ j, 0 ≤ poissonWeight z j :=
    fun j => (hmass.1 j).1
  have hweight_summable : Summable (poissonWeight z) := hmass.2.1.summable
  let f : ℕ → ℝ := fun j => if i ≤ j then poissonWeight z j else 0
  have hf_nonneg : ∀ j, 0 ≤ f j := by
    intro j
    by_cases hij : i ≤ j
    · simp [f, hij, hweight_nonneg j]
    · simp [f, hij]
  have hf_le : ∀ j, f j ≤ poissonWeight z j := by
    intro j
    by_cases hij : i ≤ j
    · simp [f, hij]
    · simp [f, hij, hweight_nonneg j]
  have hf_summable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg hf_le hweight_summable
  have hterm (j : ℕ) :
      (if (i : ℝ) ≤ (j : ℝ) then ENNReal.ofReal (poissonWeight z j) else 0).toReal = f j := by
    by_cases hij : i ≤ j
    · have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      simp [f, hij, hcast, hweight_nonneg j]
    · have hcast : ¬ (i : ℝ) ≤ (j : ℝ) := by
        intro hc
        exact hij (by exact_mod_cast hc)
      simp [f, hij, hcast]
  unfold poissonTail poissonTailENN
  rw [ENNReal.tsum_toReal_eq (by intro j; split_ifs <;> simp)]
  simp_rw [hterm]
  simp [f]

theorem S5_E05Statement_of_deps
    (hPreTails : ThresholdFoundations.PreTailsStatement)
    (hE01 : ThLean.BP.S5.S5_E01Statement) :
    ThLean.BP.S5.S5_E05Statement := by
  rcases hPreTails with ⟨_, _, _, hshift⟩
  intro z hz i hi
  rw [← poissonTail_real_tsum hE01 z hz i]
  exact hshift z hz i hi

example (hPreTails : ThresholdFoundations.PreTailsStatement)
    (hE01 : ThLean.BP.S5.S5_E01Statement) :
    ThLean.BP.S5.S5_E05Statement :=
  S5_E05Statement_of_deps hPreTails hE01

end ThLean.W.S510

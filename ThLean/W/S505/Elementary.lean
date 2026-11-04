module

public import ThLean.BP.S5.Elementary

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S505
open ThresholdFoundations

/-- The elementary Poisson kernel facts used by the low degree argument. -/
theorem S5_E01Statement_holds : ThLean.BP.S5.S5_E01Statement := by
  constructor
  · intro z hz
    have hexp := NormedSpace.expSeries_div_hasSum_exp (z : ℝ)
    have hnorm : HasSum (poissonWeight z) 1 := by
      convert! (hexp.mul_left (Real.exp (-z))) using 1
      · ext j
        change Real.exp (-z) * z ^ j / (j.factorial : ℝ) =
          Real.exp (-z) * (z ^ j / (j.factorial : ℝ))
        exact mul_div_assoc _ _ _
      · simp [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    have hpos : ∀ j : ℕ, 0 ≤ poissonWeight z j := by
      intro j
      simp only [poissonWeight]
      positivity
    have hbound : ∀ j : ℕ, poissonWeight z j ≤ 1 := by
      intro j
      have h := sum_le_hasSum ({j} : Finset ℕ) (fun i hi => hpos i) hnorm
      simpa using h
    refine ⟨?_, hnorm, ?_, ?_⟩
    · intro j
      exact ⟨hpos j, hbound j⟩
    · intro a ha
      have hgen0 :=
        (NormedSpace.expSeries_div_hasSum_exp (z * a)).mul_left (Real.exp (-z))
      have hgen : HasSum (fun j : ℕ => poissonWeight z j * a ^ j)
          (Real.exp (z * (a - 1))) := by
        convert! hgen0 using 1
        · ext j
          simp_rw [poissonWeight, mul_div_assoc, mul_pow]
          ring
        · simp [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
          ring
      exact hgen
    · intro B b hB hb
      have hsumB : Summable (fun j : ℕ => poissonWeight z j * B) :=
        hnorm.summable.mul_right B
      have hhasB : HasSum (fun j : ℕ => poissonWeight z j * B) B := by
        simpa [mul_comm] using hnorm.mul_right B
      have hsumMix : Summable (fun j : ℕ => poissonWeight z j * b j) :=
        Summable.of_nonneg_of_le
          (fun j => mul_nonneg (hpos j) (hb j).1)
          (fun j => mul_le_mul_of_nonneg_left (hb j).2 (hpos j))
          hsumB
      refine ⟨hsumMix, ?_, ?_⟩
      · change 0 ≤ ∑' j : ℕ, poissonWeight z j * b j
        exact tsum_nonneg (fun j => mul_nonneg (hpos j) (hb j).1)
      · change ∑' j : ℕ, poissonWeight z j * b j ≤ B
        calc
          ∑' j : ℕ, poissonWeight z j * b j ≤
              ∑' j : ℕ, poissonWeight z j * B :=
            hsumMix.tsum_le_tsum
              (fun j => mul_le_mul_of_nonneg_left (hb j).2 (hpos j)) hsumB
          _ = B := by rw [hhasB.tsum_eq]
  · intro j
    unfold poissonWeight
    fun_prop

end ThLean.W.S505

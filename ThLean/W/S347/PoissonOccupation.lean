module

public import ThLean.BP.S3.Poisson

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThLean.W.S347
open ThresholdFoundations

theorem S3_41aStatement_of_deps
    (h40 : ThLean.BP.S3.S3_40Statement) :
    ThLean.BP.S3.S3_41aStatement := by
  intro a p hp
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hnonneg (m : ℕ) :
      0 ≤ᵐ[μ] (fun t : ℝ => poissonWeight (p * t) m) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hz : 0 ≤ p * t := mul_nonneg hp.le ht.le
    simp only [poissonWeight]
    positivity
  have hweight_meas (m : ℕ) :
      Measurable (fun t : ℝ => ENNReal.ofReal (poissonWeight (p * t) m)) := by
    fun_prop [poissonWeight]
  have hterm_meas (m : ℕ) :
      Measurable (fun t : ℝ => ENNReal.ofReal (poissonWeight (p * t) m) * a m) := by
    fun_prop [poissonWeight]
  have hweight_lintegral (m : ℕ) :
      (∫⁻ t : ℝ in Set.Ioi 0, ENNReal.ofReal (poissonWeight (p * t) m)) =
        ENNReal.ofReal (1 / p) := by
    have hm := h40 p m hp
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hm.1 (hnonneg m), hm.2]
  have hterm_lintegral (m : ℕ) :
      (∫⁻ t : ℝ in Set.Ioi 0,
        ENNReal.ofReal (poissonWeight (p * t) m) * a m) =
        ENNReal.ofReal (1 / p) * a m := by
    rw [lintegral_mul_const (a m) (hweight_meas m), hweight_lintegral]
  calc
    (∫⁻ t : ℝ in Set.Ioi 0, poissonMixtureENN (p * t) a) =
        ∫⁻ t : ℝ in Set.Ioi 0,
          ∑' m : ℕ, ENNReal.ofReal (poissonWeight (p * t) m) * a m := rfl
    _ = ∑' m : ℕ, (∫⁻ t : ℝ in Set.Ioi 0,
          ENNReal.ofReal (poissonWeight (p * t) m) * a m) := by
      exact lintegral_tsum (fun m => (hterm_meas m).aemeasurable)
    _ = ∑' m : ℕ, ENNReal.ofReal (1 / p) * a m :=
      tsum_congr hterm_lintegral
    _ = ENNReal.ofReal (1 / p) * ∑' m : ℕ, a m := by
      rw [ENNReal.tsum_mul_left]

end ThLean.W.S347

example (h40 : ThLean.BP.S3.S3_40Statement) :
    ThLean.BP.S3.S3_41aStatement := ThLean.W.S347.S3_41aStatement_of_deps h40

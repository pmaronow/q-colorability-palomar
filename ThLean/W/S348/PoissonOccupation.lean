import ThLean.BP.S3.Poisson

noncomputable section

open MeasureTheory
open scoped BigOperators Topology ENNReal

attribute [local instance] Classical.propDecidable

namespace ThLean.W.S348

open ThresholdFoundations

/-- The real occupation identity follows from the nonnegative ENNReal identity. -/
theorem S3_41bStatement_of_deps
    (h31 : ThLean.BP.S3.S3_31Statement)
    (h41a : ThLean.BP.S3.S3_41aStatement) :
    ThLean.BP.S3.S3_41bStatement := by
  intro a p ha hp hfinite
  have hsumNN : Summable (fun m : ℕ => ENNReal.toNNReal (ENNReal.ofReal (a m))) :=
    ENNReal.summable_toNNReal_of_tsum_ne_top hfinite
  have hsumACoe : Summable
      (fun m : ℕ => ((ENNReal.toNNReal (ENNReal.ofReal (a m)) : NNReal) : ℝ)) :=
    NNReal.summable_coe.mpr hsumNN
  have hsumA : Summable a := by
    have heq :
        (fun m : ℕ => ((ENNReal.toNNReal (ENNReal.ofReal (a m)) : NNReal) : ℝ)) = a := by
      funext m
      simp [ENNReal.ofReal, ha m]
    rw [← heq]
    exact hsumACoe

  let b : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (a m)
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi 0)
  have hbMeas (m : ℕ) : Measurable
      (fun t : ℝ => ENNReal.ofReal (poissonWeight (p * t) m) * b m) := by
    dsimp [b, poissonWeight]
    fun_prop
  have hmixMeas : AEMeasurable (fun t : ℝ => poissonMixtureENN (p * t) b) μ := by
    change AEMeasurable
      (fun t : ℝ => ∑' m, ENNReal.ofReal (poissonWeight (p * t) m) * b m) μ
    exact AEMeasurable.tsum (fun m => (hbMeas m).aemeasurable)
  have hmixIntegral :
      (∫⁻ t in Set.Ioi 0, poissonMixtureENN (p * t) b) =
        ENNReal.ofReal (1 / p) * ∑' m, b m := by
    exact h41a b p hp
  have hsumB : (∑' m, b m) ≠ ⊤ := hfinite
  have hmixIntegralNe :
      (∫⁻ t in Set.Ioi 0, poissonMixtureENN (p * t) b) ≠ ⊤ := by
    rw [hmixIntegral]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsumB
  have hmixToRealIntegrable :
      Integrable (fun t : ℝ => (poissonMixtureENN (p * t) b).toReal) μ := by
    exact integrable_toReal_of_lintegral_ne_top hmixMeas hmixIntegralNe

  have hpointwise (t : ℝ) (ht : 0 < t) :
      poissonMixture (p * t) a = (poissonMixtureENN (p * t) b).toReal ∧
        ENNReal.ofReal (poissonMixture (p * t) a) = poissonMixtureENN (p * t) b := by
    have hz : 0 ≤ p * t := mul_nonneg hp.le ht.le
    rcases h31 (p * t) hz with ⟨hwNonneg, hwSummable, hwTotal, _⟩
    have hwLeOne (m : ℕ) : poissonWeight (p * t) m ≤ 1 := by
      calc
        poissonWeight (p * t) m ≤ ∑' k, poissonWeight (p * t) k :=
          hwSummable.le_tsum m (fun k _ => hwNonneg k)
        _ = 1 := hwTotal
    have htermNonneg (m : ℕ) :
        0 ≤ poissonWeight (p * t) m * a m := mul_nonneg (hwNonneg m) (ha m)
    have htermLe (m : ℕ) :
        poissonWeight (p * t) m * a m ≤ a m := by
      calc
        poissonWeight (p * t) m * a m ≤ 1 * a m :=
          mul_le_mul_of_nonneg_right (hwLeOne m) (ha m)
        _ = a m := one_mul _
    have htermsSummable : Summable (fun m : ℕ => poissonWeight (p * t) m * a m) :=
      Summable.of_nonneg_of_le htermNonneg htermLe hsumA
    have hmixtureENN :
        ENNReal.ofReal (poissonMixture (p * t) a) = poissonMixtureENN (p * t) b := by
      change ENNReal.ofReal (∑' m, poissonWeight (p * t) m * a m) = _
      rw [ENNReal.ofReal_tsum_of_nonneg htermNonneg htermsSummable]
      change (∑' m, ENNReal.ofReal (poissonWeight (p * t) m * a m)) =
        ∑' m, ENNReal.ofReal (poissonWeight (p * t) m) * b m
      apply tsum_congr
      intro m
      simp [b, ENNReal.ofReal_mul (hwNonneg m)]
    have hmixtureNonneg : 0 ≤ poissonMixture (p * t) a := tsum_nonneg htermNonneg
    constructor
    · calc
        poissonMixture (p * t) a =
            (ENNReal.ofReal (poissonMixture (p * t) a)).toReal :=
          (ENNReal.toReal_ofReal hmixtureNonneg).symm
        _ = (poissonMixtureENN (p * t) b).toReal := congrArg ENNReal.toReal hmixtureENN
    · exact hmixtureENN

  have hrealEq :
      (fun t : ℝ => poissonMixture (p * t) a) =ᵐ[μ]
        (fun t => (poissonMixtureENN (p * t) b).toReal) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hpointwise t ht).1
  have hrealIntegrable : Integrable (fun t : ℝ => poissonMixture (p * t) a) μ :=
    hmixToRealIntegrable.congr hrealEq.symm
  have hrealNonneg :
      0 ≤ᵐ[μ] (fun t : ℝ => poissonMixture (p * t) a) := by
    filter_upwards [hrealEq] with t ht
    rw [ht]
    exact ENNReal.toReal_nonneg
  refine ⟨hsumA, ?_, ?_⟩
  · exact hrealIntegrable
  · have hIntegralToReal :
        (∫ t in Set.Ioi 0, poissonMixture (p * t) a) =
          (∫⁻ t in Set.Ioi 0, ENNReal.ofReal (poissonMixture (p * t) a)).toReal :=
      integral_eq_lintegral_of_nonneg_ae hrealNonneg hrealIntegrable.aestronglyMeasurable
    have hlintegralEq :
        (∫⁻ t in Set.Ioi 0, ENNReal.ofReal (poissonMixture (p * t) a)) =
          ∫⁻ t in Set.Ioi 0, poissonMixtureENN (p * t) b := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hpointwise t ht).2
    rw [hIntegralToReal, hlintegralEq, hmixIntegral]
    rw [← ENNReal.ofReal_tsum_of_nonneg ha hsumA]
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.toReal_ofReal
      (mul_nonneg (by positivity) (tsum_nonneg ha))

end ThLean.W.S348

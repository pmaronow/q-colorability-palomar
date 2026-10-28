import ThLean.BP.S5.Poisson

noncomputable section

open MeasureTheory
open scoped BigOperators Topology ENNReal

namespace ThLean.W.S552

open ThresholdFoundations

theorem S5_10Statement_of_deps
    (hpre : ThresholdFoundations.PrePoissonStatement)
    (hE07 : ThLean.BP.S5.S5_E07Statement)
    (hE08 : ThLean.BP.S5.S5_E08Statement) :
    ThLean.BP.S5.S5_10Statement := by
  intro p hp
  constructor
  · intro a
    let μ : Measure ℝ := volume.restrict (Set.Ici (0 : ℝ))
    have hkernelMeas (m : ℕ) :
        Measurable (fun t : ℝ => ENNReal.ofReal (poissonWeight (p * t) m)) := by
      have hc : Continuous (fun t : ℝ => poissonWeight (p * t) m) := by
        dsimp [poissonWeight]
        fun_prop
      exact ENNReal.measurable_ofReal.comp hc.measurable
    have htermMeas (m : ℕ) :
        Measurable (fun t : ℝ =>
          ENNReal.ofReal (poissonWeight (p * t) m) * a m) := by
      exact (hkernelMeas m).mul measurable_const
    have hmeas : Measurable (fun t : ℝ => poissonMixtureENN (p * t) a) := by
      apply Measurable.tsum
      intro m
      exact htermMeas m
    have hnonneg (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
        0 ≤ poissonWeight (p * t) m := by
      exact (hpre.1 (p * t) (mul_nonneg hp.le ht)).2.2 m
    have hkernel (m : ℕ) :
        ∫⁻ t in Set.Ici (0 : ℝ),
          ENNReal.ofReal (poissonWeight (p * t) m) = ENNReal.ofReal (1 / p) := by
      have hkernelAE :
          0 ≤ᵐ[μ] fun t : ℝ => poissonWeight (p * t) m := by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact hnonneg m t ht
      rw [← ofReal_integral_eq_lintegral_ofReal (hE07.1 m p hp).1 hkernelAE]
      rw [(hE07.1 m p hp).2]
    have htermIntegral (m : ℕ) :
        ∫⁻ t in Set.Ici (0 : ℝ),
          ENNReal.ofReal (poissonWeight (p * t) m) * a m =
            ENNReal.ofReal (1 / p) * a m := by
      rw [lintegral_mul_const'' (a m) (hkernelMeas m).aemeasurable]
      rw [hkernel]
    have htonelli :
        (∫⁻ t in Set.Ici (0 : ℝ), poissonMixtureENN (p * t) a) =
          ∑' m : ℕ, ∫⁻ t in Set.Ici (0 : ℝ),
            ENNReal.ofReal (poissonWeight (p * t) m) * a m := by
      simpa only [poissonMixtureENN] using
        (hE08.1 ℝ ℕ μ
          (fun m t => ENNReal.ofReal (poissonWeight (p * t) m) * a m)
          (fun m => (htermMeas m).aemeasurable))
    constructor
    · exact hmeas.comp measurable_subtype_coe
    · calc
        (∫⁻ t in Set.Ici (0 : ℝ), poissonMixtureENN (p * t) a) =
            ∑' m : ℕ, ∫⁻ t in Set.Ici (0 : ℝ),
              ENNReal.ofReal (poissonWeight (p * t) m) * a m := htonelli
        _ = ∑' m : ℕ, ENNReal.ofReal (1 / p) * a m := tsum_congr htermIntegral
        _ = ENNReal.ofReal (1 / p) * ∑' m : ℕ, a m := ENNReal.tsum_mul_left
  · intro a ha_nonneg ha_sum
    let μ : Measure ℝ := volume.restrict (Set.Ici (0 : ℝ))
    let aENN : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (a m)
    have hENN : ∀ z : ℝ, 0 ≤ z →
        (∑' m : ℕ, ENNReal.ofReal (poissonWeight z m) * aENN m) =
          ENNReal.ofReal (poissonMixture z a) := by
      intro z hz
      have hw_nonneg (m : ℕ) : 0 ≤ poissonWeight z m :=
        (hpre.1 z hz).2.2 m
      have hw_le (m : ℕ) : poissonWeight z m ≤ 1 := by
        calc
          poissonWeight z m ≤ ∑' k : ℕ, poissonWeight z k :=
            (hpre.1 z hz).1.le_tsum m (fun k _ => (hpre.1 z hz).2.2 k)
          _ = 1 := (hpre.1 z hz).2.1
      have hweighted_nonneg (m : ℕ) :
          0 ≤ poissonWeight z m * a m := mul_nonneg (hw_nonneg m) (ha_nonneg m)
      have hweighted_le (m : ℕ) :
          poissonWeight z m * a m ≤ a m := by
        calc
          poissonWeight z m * a m ≤ 1 * a m :=
            mul_le_mul_of_nonneg_right (hw_le m) (ha_nonneg m)
          _ = a m := one_mul _
      have hweighted_sum : Summable (fun m : ℕ => poissonWeight z m * a m) :=
        ha_sum.of_nonneg_of_le hweighted_nonneg hweighted_le
      unfold poissonMixture
      calc
        (∑' m : ℕ, ENNReal.ofReal (poissonWeight z m) * aENN m) =
            ∑' m : ℕ, ENNReal.ofReal (poissonWeight z m * a m) := by
              apply tsum_congr
              intro m
              simpa [aENN] using (ENNReal.ofReal_mul (hw_nonneg m)).symm
        _ = ENNReal.ofReal (∑' m : ℕ, poissonWeight z m * a m) :=
          (ENNReal.ofReal_tsum_of_nonneg hweighted_nonneg hweighted_sum).symm
    have hkernelMeas (m : ℕ) :
        Measurable (fun t : ℝ => ENNReal.ofReal (poissonWeight (p * t) m)) := by
      have hc : Continuous (fun t : ℝ => poissonWeight (p * t) m) := by
        dsimp [poissonWeight]
        fun_prop
      exact ENNReal.measurable_ofReal.comp hc.measurable
    have htermMeas (m : ℕ) :
        Measurable (fun t : ℝ =>
          ENNReal.ofReal (poissonWeight (p * t) m) * aENN m) := by
      exact (hkernelMeas m).mul measurable_const
    have hmeas : Measurable (fun t : ℝ => poissonMixtureENN (p * t) aENN) := by
      apply Measurable.tsum
      intro m
      exact htermMeas m
    have hfiniteCoeff : (∑' m : ℕ, aENN m) < ∞ := by
      exact ha_sum.tsum_ofReal_lt_top
    have hkernel (m : ℕ) :
        ∫⁻ t in Set.Ici (0 : ℝ),
          ENNReal.ofReal (poissonWeight (p * t) m) = ENNReal.ofReal (1 / p) := by
      have hkernelAE :
          0 ≤ᵐ[μ] fun t : ℝ => poissonWeight (p * t) m := by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact (hpre.1 (p * t) (mul_nonneg hp.le ht)).2.2 m
      rw [← ofReal_integral_eq_lintegral_ofReal (hE07.1 m p hp).1 hkernelAE]
      rw [(hE07.1 m p hp).2]
    have htermIntegral (m : ℕ) :
        ∫⁻ t in Set.Ici (0 : ℝ),
          ENNReal.ofReal (poissonWeight (p * t) m) * aENN m =
            ENNReal.ofReal (1 / p) * aENN m := by
      rw [lintegral_mul_const'' (aENN m) (hkernelMeas m).aemeasurable]
      rw [hkernel]
    have htonelli :
        (∫⁻ t in Set.Ici (0 : ℝ), poissonMixtureENN (p * t) aENN) =
          ∑' m : ℕ, ∫⁻ t in Set.Ici (0 : ℝ),
            ENNReal.ofReal (poissonWeight (p * t) m) * aENN m := by
      simpa only [poissonMixtureENN] using
        (hE08.1 ℝ ℕ μ
          (fun m t => ENNReal.ofReal (poissonWeight (p * t) m) * aENN m)
          (fun m => (htermMeas m).aemeasurable))
    have hocc :
        (∫⁻ t in Set.Ici (0 : ℝ), poissonMixtureENN (p * t) aENN) =
          ENNReal.ofReal (1 / p) * ∑' m : ℕ, aENN m := by
      calc
        _ = ∑' m : ℕ, ∫⁻ t in Set.Ici (0 : ℝ),
              ENNReal.ofReal (poissonWeight (p * t) m) * aENN m := htonelli
        _ = ∑' m : ℕ, ENNReal.ofReal (1 / p) * aENN m := tsum_congr htermIntegral
        _ = ENNReal.ofReal (1 / p) * ∑' m : ℕ, aENN m := ENNReal.tsum_mul_left
    have hocc_finite :
        (∫⁻ t in Set.Ici (0 : ℝ), poissonMixtureENN (p * t) aENN) ≠ ∞ := by
      rw [hocc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfiniteCoeff.ne
    have hconvert := hE08.2.1 ℝ μ
      (fun t : ℝ => poissonMixtureENN (p * t) aENN) hmeas.aemeasurable hocc_finite
    have hpoint (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
        (poissonMixtureENN (p * t) aENN).toReal = poissonMixture (p * t) a := by
      have hz : 0 ≤ p * t := mul_nonneg hp.le ht
      have h := hENN (p * t) hz
      have hsum_nonneg :
          0 ≤ ∑' m : ℕ, poissonWeight (p * t) m * a m :=
        tsum_nonneg (fun m => mul_nonneg
          ((hpre.1 (p * t) hz).2.2 m) (ha_nonneg m))
      change (∑' m : ℕ,
        ENNReal.ofReal (poissonWeight (p * t) m) * aENN m).toReal = _
      rw [h]
      exact ENNReal.toReal_ofReal (by simpa [poissonMixture] using hsum_nonneg)
    have hpointAE :
        (fun t : ℝ => (poissonMixtureENN (p * t) aENN).toReal) =ᵐ[μ]
          fun t : ℝ => poissonMixture (p * t) a := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact hpoint t ht
    have hsumCoeffENN :
        (∑' m : ℕ, aENN m) = ENNReal.ofReal (∑' m : ℕ, a m) :=
      by simpa [aENN] using (ENNReal.ofReal_tsum_of_nonneg ha_nonneg ha_sum).symm
    constructor
    · change Integrable (fun t : ℝ => poissonMixture (p * t) a) μ
      exact hconvert.2.1.congr hpointAE
    · calc
        (∫ t in Set.Ici (0 : ℝ), poissonMixture (p * t) a) =
            ∫ t, (poissonMixtureENN (p * t) aENN).toReal ∂μ :=
              integral_congr_ae hpointAE.symm
        _ = (∫⁻ t in Set.Ici (0 : ℝ), poissonMixtureENN (p * t) aENN).toReal :=
          hconvert.2.2
        _ = (1 / p) * ∑' m : ℕ, a m := by
          rw [hocc, hsumCoeffENN, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (div_nonneg (by norm_num) hp.le),
            ENNReal.toReal_ofReal (tsum_nonneg ha_nonneg)]

end ThLean.W.S552

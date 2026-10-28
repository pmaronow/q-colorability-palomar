import ThLean.BP.S5.Identification

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S527
open ThresholdFoundations ThLean.BP.S5

theorem S5_24Statement_of_deps
    (h22 : S5_22Statement) (hE04 : S5_E04Statement)
    (hE01 : S5_E01Statement) (hE08 : S5_E08Statement) :
    S5_24Statement := by
  intro q N D k hq hN hD h4 hk
  have hqR : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast (show 1 < q by omega)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hB : 0 < lowMeanBound q := by
    unfold lowMeanBound
    positivity
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by omega)
  have hkR : 0 < (k : ℝ) := by
    have hleft : 0 ≤ Real.exp 1 * (D : ℝ) * lowMeanBound q := by positivity
    linarith
  have hdata := h22 q N D hq hN hD h4
  have hcapPos : 0 < lowTimeCap q N := hdata.2.2.2.2.2.2.1
  have hkpos : 1 ≤ k := by
    have hkNat : 0 < k := by exact_mod_cast hkR
    omega
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, hmean⟩
  let C : ℝ := (Real.exp 1 * (D : ℝ) * lowMeanBound q / (k : ℝ)) ^ k
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCnonneg : 0 ≤ C := le_of_lt hCpos
  have hpoint : ∀ s : ℝ, 0 ≤ s → s ≤ lowTimeCap q N →
      (∑' j : ℕ, if k < j then poissonWeight (D * neighborMean N D s) j else 0) ≤ C := by
    intro s hs0 hsCap
    have hnb := hmean s hs0 hsCap
    have hμ0 : 0 ≤ (D : ℝ) * neighborMean N D s := by
      exact mul_nonneg (Nat.cast_nonneg D) hnb.1
    have hμle : (D : ℝ) * neighborMean N D s ≤ (D : ℝ) * lowMeanBound q := by
      exact mul_le_mul_of_nonneg_left hnb.2 (Nat.cast_nonneg D)
    have htail := (hE04 (D * neighborMean N D s) hμ0).2 k hkpos
    rcases htail with ⟨_, _, htail⟩
    have hnum : Real.exp 1 * (D * neighborMean N D s) ≤
        Real.exp 1 * (D : ℝ) * lowMeanBound q := by
      calc
        Real.exp 1 * (D * neighborMean N D s) ≤
            Real.exp 1 * ((D : ℝ) * lowMeanBound q) :=
          mul_le_mul_of_nonneg_left hμle (le_of_lt (Real.exp_pos 1))
        _ = Real.exp 1 * (D : ℝ) * lowMeanBound q := by ring
    have hbase : Real.exp 1 * (D * neighborMean N D s) / (k : ℝ) ≤
        Real.exp 1 * (D : ℝ) * lowMeanBound q / (k : ℝ) :=
      (div_le_div_iff_of_pos_right hkR).2 hnum
    calc
      (∑' j : ℕ, if k < j then poissonWeight (D * neighborMean N D s) j else 0) ≤
          (Real.exp 1 * (D * neighborMean N D s) / (k : ℝ)) ^ k := htail
      _ ≤ C := by
        dsimp [C]
        exact (pow_le_pow_left₀ (by positivity) hbase) k

  have hweights_nonneg : ∀ s : ℝ, 0 ≤ s → s ≤ lowTimeCap q N → ∀ j : ℕ,
      0 ≤ poissonWeight (D * neighborMean N D s) j := by
    intro s hs0 hsCap j
    have hnb := hmean s hs0 hsCap
    have hμ0 : 0 ≤ (D : ℝ) * neighborMean N D s :=
      mul_nonneg (Nat.cast_nonneg D) hnb.1
    exact ((hE01.1 (D * neighborMean N D s) hμ0).1 j).1

  let tailENN : ℝ → ℝ≥0∞ := fun s =>
    ∑' j : ℕ, if k < j then ENNReal.ofReal (poissonWeight (D * neighborMean N D s) j) else 0
  let tailReal : ℝ → ℝ := fun s =>
    ∑' j : ℕ, if k < j then poissonWeight (D * neighborMean N D s) j else 0

  have hweightMeas : ∀ j : ℕ,
      Measurable (fun s : ℝ => ENNReal.ofReal (poissonWeight (D * neighborMean N D s) j)) := by
    intro j
    exact ENNReal.measurable_ofReal.comp <|
      (hE01.2 j).measurable.comp (by fun_prop [neighborMean])
  have htailMeas : Measurable tailENN := by
    apply Measurable.tsum
    intro j
    by_cases hj : k < j
    · simpa [tailENN, hj] using hweightMeas j
    · simp [hj]

  have hcoeffSummable : ∀ s : ℝ, 0 ≤ s → s ≤ lowTimeCap q N →
      Summable (fun j : ℕ => if k < j then poissonWeight (D * neighborMean N D s) j else 0) := by
    intro s hs0 hsCap
    have hnb := hmean s hs0 hsCap
    have hμ0 : 0 ≤ (D : ℝ) * neighborMean N D s :=
      mul_nonneg (Nat.cast_nonneg D) hnb.1
    have hpoi := (hE01.1 (D * neighborMean N D s) hμ0).2.1.summable
    apply Summable.of_norm_bounded hpoi
    intro j
    by_cases hj : k < j
    · simp [hj, abs_of_nonneg ((hE01.1 (D * neighborMean N D s) hμ0).1 j).1]
    · simpa [hj] using ((hE01.1 (D * neighborMean N D s) hμ0).1 j).1

  have hrealNonneg : ∀ s : ℝ, 0 ≤ s → s ≤ lowTimeCap q N → 0 ≤ tailReal s := by
    intro s hs0 hsCap
    apply tsum_nonneg
    intro j
    split_ifs with hj
    · exact hweights_nonneg s hs0 hsCap j
    · exact le_rfl

  have hENN_eq : ∀ s : ℝ, 0 ≤ s → s ≤ lowTimeCap q N →
      tailENN s = ENNReal.ofReal (tailReal s) := by
    intro s hs0 hsCap
    have hterms : ∀ j : ℕ,
        0 ≤ (if k < j then poissonWeight (D * neighborMean N D s) j else 0) := by
      intro j
      split_ifs with hj
      · exact hweights_nonneg s hs0 hsCap j
      · exact le_rfl
    have hsum := ENNReal.ofReal_tsum_of_nonneg hterms (hcoeffSummable s hs0 hsCap)
    change (∑' j : ℕ, if k < j then ENNReal.ofReal (poissonWeight (D * neighborMean N D s) j) else 0) =
      ENNReal.ofReal (∑' j : ℕ, if k < j then poissonWeight (D * neighborMean N D s) j else 0)
    rw [hsum]
    apply tsum_congr
    intro j
    by_cases hj : k < j <;> simp [hj]

  have hpointENN : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) (lowTimeCap q N) →
      tailENN s ≤ ENNReal.ofReal C := by
    intro s hs
    have htail := hpoint s hs.1 hs.2
    rw [hENN_eq s hs.1 hs.2]
    exact ENNReal.ofReal_le_ofReal htail

  have hIntervalMeas : MeasurableSet (Set.Icc (0 : ℝ) (lowTimeCap q N)) := measurableSet_Icc
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) (lowTimeCap q N))
  have hboundAE : ∀ᵐ s ∂μ, tailENN s ≤ ENNReal.ofReal C := by
    rw [show μ = volume.restrict (Set.Icc (0 : ℝ) (lowTimeCap q N)) by rfl]
    exact (ae_restrict_iff' hIntervalMeas).2 <| ae_of_all volume fun s hs => hpointENN s hs
  have hlintegralBound : (∫⁻ s, tailENN s ∂μ) ≤
      ENNReal.ofReal C * volume (Set.Icc (0 : ℝ) (lowTimeCap q N)) := by
    calc
      (∫⁻ s, tailENN s ∂μ) ≤ ∫⁻ _s, ENNReal.ofReal C ∂μ := lintegral_mono_ae hboundAE
      _ = ENNReal.ofReal C * volume (Set.Icc (0 : ℝ) (lowTimeCap q N)) := by
        simp [μ, Measure.restrict_apply]
  have hvolFinite : volume (Set.Icc (0 : ℝ) (lowTimeCap q N)) < ∞ := measure_Icc_lt_top
  have hlintegralFinite : (∫⁻ s, tailENN s ∂μ) < ∞ := by
    apply lt_of_le_of_lt hlintegralBound
    exact ENNReal.mul_lt_top (by simp) hvolFinite
  have hconverted := hE08.2.1 ℝ μ tailENN htailMeas.aemeasurable (ne_of_lt hlintegralFinite)
  have htailRealIntegrable : Integrable tailReal μ := by
    apply hconverted.2.1.congr
    apply (ae_restrict_iff' hIntervalMeas).2
    exact ae_of_all volume fun s hs => by
      change (tailENN s).toReal = tailReal s
      have hEq := hENN_eq s hs.1 hs.2
      rw [hEq, ENNReal.toReal_ofReal (hrealNonneg s hs.1 hs.2)]
  have htailIntegrableOn : IntegrableOn tailReal (Set.Icc (0 : ℝ) (lowTimeCap q N)) := by
    simpa [IntegrableOn, μ] using htailRealIntegrable

  have hcapNonneg : 0 ≤ lowTimeCap q N := le_of_lt hcapPos
  have hinterval : IntervalIntegrable tailReal volume 0 (lowTimeCap q N) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hcapNonneg).2 htailIntegrableOn
  have hconst : IntervalIntegrable (fun _ : ℝ => C) volume 0 (lowTimeCap q N) :=
    intervalIntegrable_const
  refine ⟨hkpos, ?_, htailIntegrableOn, ?_⟩
  · exact hpoint
  · calc
      (∫ s in (0 : ℝ)..lowTimeCap q N, tailReal s) ≤
          ∫ s in (0 : ℝ)..lowTimeCap q N, C :=
        intervalIntegral.integral_mono_on hcapNonneg hinterval hconst (fun s hs => hpoint s hs.1 hs.2)
      _ = lowTimeCap q N * C := by simp [intervalIntegral.integral_const, sub_zero]

end ThLean.W.S527

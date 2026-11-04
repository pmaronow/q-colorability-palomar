module

public import ThLean.BP.S5.Identification

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S528
open ThLean.BP.S5 ThresholdFoundations

private theorem blocking_abs_le_one {V : Type} [Fintype V] [Nonempty V]
    (q j : ℕ) (B : MGraph V) : |blocking q B j| ≤ 1 := by
  letI : Nonempty (Fin j → V) := ⟨fun _ => Classical.choice (inferInstance : Nonempty V)⟩
  have hcard : (0 : ℝ) < Fintype.card (Fin j → V) := by positivity
  unfold blocking listMean uniformMean
  rw [abs_div, abs_of_pos hcard]
  apply (div_le_one₀ hcard).2
  have hsum_nonneg : 0 ≤ ∑ x : Fin j → V,
      indicator (Colorable q B ∧ ¬ Colorable q (addRoot B (List.ofFn x))) := by
    apply Finset.sum_nonneg
    intro x hx
    by_cases h : Colorable q B ∧ ¬ Colorable q (addRoot B (List.ofFn x)) <;>
      simp [indicator, h]
  have hsum_le : (∑ x : Fin j → V,
      indicator (Colorable q B ∧ ¬ Colorable q (addRoot B (List.ofFn x)))) ≤
      (Fintype.card (Fin j → V) : ℝ) := by
    calc
      _ ≤ ∑ _x : Fin j → V, (1 : ℝ) := Finset.sum_le_sum fun x hx => by
        by_cases h : Colorable q B ∧ ¬ Colorable q (addRoot B (List.ofFn x)) <;>
          simp [indicator, h]
      _ = (Fintype.card (Fin j → V) : ℝ) := by simp
  rw [abs_of_nonneg hsum_nonneg]
  exact hsum_le

private theorem poissonWeight_nonneg {z : ℝ} (hz : 0 ≤ z) (j : ℕ) :
    0 ≤ poissonWeight z j := by
  unfold poissonWeight
  positivity

/-- The leaf estimate follows from the five comparison, hazard, parameter, and
measurability leaves used in its proof. -/
theorem S5_25Statement_of_deps
    (h11 : ThLean.BP.S5.S5_11Statement)
    (h14 : ThLean.BP.S5.S5_14Statement)
    (h15B : ThLean.BP.S5.S5_15BStatement)
    (h22 : ThLean.BP.S5.S5_22Statement)
    (h08C : ThLean.BP.S5.S5_08CStatement) :
    ThLean.BP.S5.S5_25Statement := by
  intro q N D k hq hN hD h4 Z
  let U : Type := {v : Fin N // v ∉ Z.val}
  let r : ℝ := lowEdgeRate N
  let p : ℝ := augmentedRate N D
  let T : ℝ := lowTimeCap q N
  have hparams := h22 q N D hq hN hD h4
  rcases hparams with
    ⟨h2q, h2N, hDN, hUlower, hrpos, hppos, hTpos, hinv, hratio, hratio2, hmean⟩
  have hUcard : Fintype.card U = N - D := by
    dsimp [U]
    rw [Fintype.card_subtype_compl]
    simp [Z.property]
  have hUcard_le : 2 ≤ Fintype.card U := by omega
  have hUnonempty : Nonempty U := Fintype.card_pos_iff.mp (by omega)
  have hOptionCard : 2 ≤ Fintype.card (Option U) := by
    rw [Fintype.card_option]
    omega
  have hr_nonneg : 0 ≤ r := le_of_lt hrpos
  have hp_pos : 0 < p := hppos
  have hrate_nonneg : ∀ e : Sym2 U, 0 ≤ perPairRate r e := by
    intro e
    by_cases he : ∃ v, e = s(v, v)
    · simp [perPairRate, he]
    · simp [perPairRate, he, hr_nonneg]
  have hrate_mul (t : ℝ) (e : Sym2 U) : perPairRate r e * t = perPairRate (r * t) e := by
    by_cases he : ∃ v, e = s(v, v)
    · simp [perPairRate, he]
    · simp [perPairRate, he]
  have hblock_meas (j : ℕ) : Measurable (fun t : Set.Ici (0 : ℝ) =>
      blockingMean (V := U) q (r * t.val) j) := by
    have h := h08C (I := Sym2 U) (fun e => perPairRate r e) hrate_nonneg
      (fun G : Sym2 U → ℕ => blocking q G j)
      ⟨1, fun G => blocking_abs_le_one q j G⟩
    convert h using 1
    funext t
    simp only [blockingMean, countMean, independentPoissonGraphMean,
      independentPoissonGraphMass]
    congr 1
    funext G
    apply congrArg (fun x : ℝ => x * blocking q G j)
    apply Finset.prod_congr rfl
    intro e he
    exact (congrArg (fun x => poissonWeight x (G e)) (hrate_mul t.val e)).symm
  have hadded_meas : Measurable (fun t : Set.Ici (0 : ℝ) =>
      addedFailure (V := U) q (r * t.val) (neighborMean N D t.val)) := by
    change Measurable (fun t : Set.Ici (0 : ℝ) =>
      ∑' j : ℕ, poissonWeight (neighborMean N D t.val) j *
        blockingMean (V := U) q (r * t.val) j)
    apply Measurable.tsum
    intro j
    apply Measurable.mul
    · dsimp [poissonWeight, neighborMean, r]
      fun_prop
    · exact hblock_meas j
  have hpow_nonneg : 0 ≤ (D : ℝ)^k := by positivity
  have hexp_nonneg : 0 ≤ Real.exp (lowMeanBound q) - 1 := by
    have hmean0 : 0 ≤ lowMeanBound q := by
      have hz := hmean 0 (le_rfl) (by simpa [T] using le_of_lt hTpos)
      exact le_trans hz.1 hz.2
    have he : 1 ≤ Real.exp (lowMeanBound q) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hmean0
    linarith
  let C : ℝ := (D : ℝ)^k * (Real.exp (lowMeanBound q) - 1)
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  let g : ℝ → ℝ := fun s => poissonGraphMean (p * s) (kappa (V := Option U) q)
  let f : ℝ → ℝ := fun s => (D : ℝ)^k *
    addedFailure (V := U) q (r * s) (neighborMean N D s)
  have harg (s : ℝ) : r * (Fintype.card U : ℝ) * s = neighborMean N D s := by
    simp [neighborMean, r, hUcard]
  have htime (s : ℝ) : r * ((Fintype.card U + 1).choose 2 : ℝ) * s = p * s := by
    simp [r, p, augmentedRate, hUcard]
  have hcomp : ∀ s ∈ Set.Icc (0 : ℝ) T, f s ≤ C * g s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hsT : s ≤ T := hs.2
    have hm := hmean s hs0 hsT
    let a : ℕ → ℝ := incrementMean (V := U) q (r * s)
    let b : ℕ → ℝ := blockingMean (V := U) q (r * s)
    have h15 := h15B U q hq hUcard_le r s hrpos hs0
    have ha : ∀ j, 0 ≤ a j := h15.1
    have hb : ∀ j, b j = ∑ i ∈ Finset.range j, a i := h15.2.2.1
    have hbb : ∀ j, 0 ≤ b j ∧ b j ≤ 1 := h15.2.1
    have hz_nonneg : 0 ≤ neighborMean N D s := hm.1
    have htilt := h14 a b ha hb hbb (neighborMean N D s) hz_nonneg
    have hmix_id := h15.2.2.2
    have hmix_id' : poissonMixture (neighborMean N D s) a = g s := by
      simpa [g, harg s, htime s] using hmix_id
    have hfailure_le :
        addedFailure (V := U) q (r * s) (neighborMean N D s) ≤
          (Real.exp (neighborMean N D s) - 1) * g s := by
      change poissonMixture (neighborMean N D s) b ≤ _
      calc
        poissonMixture (neighborMean N D s) b ≤
            (Real.exp (neighborMean N D s) - 1) * poissonMixture (neighborMean N D s) a :=
          htilt.2.2
        _ = (Real.exp (neighborMean N D s) - 1) * g s := by rw [hmix_id']
    have hg_nonneg : 0 ≤ g s := by
      have hterms : ∀ j, 0 ≤ poissonWeight (neighborMean N D s) j * a j := by
        intro j
        exact mul_nonneg (poissonWeight_nonneg hz_nonneg j) (ha j)
      have hmix0 : 0 ≤ poissonMixture (neighborMean N D s) a := tsum_nonneg hterms
      rw [← hmix_id']
      exact hmix0
    have hexpz_le : Real.exp (neighborMean N D s) - 1 ≤
        Real.exp (lowMeanBound q) - 1 := by
      exact sub_le_sub_right (Real.exp_le_exp.mpr hm.2) 1
    have hpowfail : 0 ≤ f s := by
      have hterms : ∀ j, 0 ≤ poissonWeight (neighborMean N D s) j * b j := by
        intro j
        exact mul_nonneg (poissonWeight_nonneg hz_nonneg j) (hbb j).1
      have hmix0 : 0 ≤ poissonMixture (neighborMean N D s) b := tsum_nonneg hterms
      simpa [f, C, addedFailure, b] using mul_nonneg hpow_nonneg hmix0
    dsimp [f, C]
    calc
      (D : ℝ)^k * addedFailure (V := U) q (r * s) (neighborMean N D s)
          ≤ (D : ℝ)^k * ((Real.exp (neighborMean N D s) - 1) * g s) :=
            mul_le_mul_of_nonneg_left hfailure_le hpow_nonneg
      _ ≤ (D : ℝ)^k * ((Real.exp (lowMeanBound q) - 1) * g s) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexpz_le hg_nonneg) hpow_nonneg
      _ = C * g s := by ring
  have hbaseData := h11 (Option U) q hq hOptionCard
  have hbase := hbaseData.2 p hp_pos
  have hbaseInt : IntegrableOn g (Set.Ici 0) := by
    simpa [g] using hbase.1
  have hbase_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ici (0 : ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    exact (show 0 ≤ g s from by
      have hs0 : 0 ≤ s := hs
      have hz0 : 0 ≤ neighborMean N D s := by
        simp [neighborMean]
        positivity
      let a : ℕ → ℝ := incrementMean (V := U) q (r * s)
      have h15 := h15B U q hq hUcard_le r s hrpos hs0
      have hterms : ∀ j, 0 ≤ poissonWeight (neighborMean N D s) j * a j := by
        intro j
        exact mul_nonneg (poissonWeight_nonneg hz0 j) (h15.1 j)
      have hmix0 : 0 ≤ poissonMixture (neighborMean N D s) a := tsum_nonneg hterms
      have hmix_id := h15.2.2.2
      have hmix_id' : poissonMixture (neighborMean N D s) a = g s := by
        simpa [g, harg s, htime s] using hmix_id
      rw [← hmix_id']
      exact hmix0)
  have hbaseIcc : IntegrableOn g (Set.Icc (0 : ℝ) T) :=
    hbaseInt.mono_set (by intro s hs; exact hs.1)
  have hbaseIcc_sub : Integrable (fun x : Set.Icc (0 : ℝ) T => g x.val)
      (volume.comap (Subtype.val : Set.Icc (0 : ℝ) T → ℝ)) := by
    exact (integrableOn_iff_comap_subtypeVal (f := g) (s := Set.Icc (0 : ℝ) T)
      measurableSet_Icc).mp hbaseIcc
  have hmajorSub : Integrable (fun x : Set.Icc (0 : ℝ) T => C * g x.val)
      (volume.comap (Subtype.val : Set.Icc (0 : ℝ) T → ℝ)) := hbaseIcc_sub.const_mul C
  have htargetMeasSub : Measurable (fun x : Set.Icc (0 : ℝ) T => f x.val) := by
    have hincl : Measurable (fun x : Set.Icc (0 : ℝ) T =>
        (⟨x.val, x.property.1⟩ : Set.Ici (0 : ℝ))) := by fun_prop
    dsimp [f]
    exact measurable_const.mul (hadded_meas.comp hincl)
  have hfn_all : ∀ x : Set.Icc (0 : ℝ) T, 0 ≤ f x.val := by
    intro x
    have hfn : 0 ≤ f x.val := by
      have hs0 : 0 ≤ x.val := x.property.1
      have hm := hmean x.val hs0 x.property.2
      let b : ℕ → ℝ := blockingMean (V := U) q (r * x.val)
      have h15 := h15B U q hq hUcard_le r x.val hrpos hs0
      have hterms : ∀ j, 0 ≤ poissonWeight (neighborMean N D x.val) j * b j := by
        intro j
        exact mul_nonneg (poissonWeight_nonneg hm.1 j) (h15.2.1 j).1
      have hmix0 : 0 ≤ poissonMixture (neighborMean N D x.val) b := tsum_nonneg hterms
      simpa [f, b, addedFailure] using mul_nonneg hpow_nonneg hmix0
    exact hfn
  have htargetSub : Integrable (fun x : Set.Icc (0 : ℝ) T => f x.val)
      (volume.comap (Subtype.val : Set.Icc (0 : ℝ) T → ℝ)) := by
    apply hmajorSub.mono_nonneg htargetMeasSub.aestronglyMeasurable
    · exact ae_of_all _ hfn_all
    · exact ae_of_all _ (fun x => hcomp x.val x.property)
  have htargetIcc : IntegrableOn f (Set.Icc (0 : ℝ) T) := by
    exact (integrableOn_iff_comap_subtypeVal (f := f) (s := Set.Icc (0 : ℝ) T)
      measurableSet_Icc).mpr htargetSub
  have hbaseIntegralBound : (∫ s in Set.Ici (0 : ℝ), g s) ≤ 1 / p := by
    simpa [g] using hbase.2
  have hIocBound : (∫ s in Set.Ioc (0 : ℝ) T, g s) ≤
      (∫ s in Set.Ici (0 : ℝ), g s) := by
    apply integral_mono_measure
      (Measure.restrict_mono (show Set.Ioc (0 : ℝ) T ⊆ Set.Ici 0 from
        fun _ hs => le_of_lt hs.1) le_rfl)
      hbase_nonneg hbaseInt.integrable
  have hT : (0 : ℝ) ≤ T := le_of_lt hTpos
  have hbaseInterval : IntervalIntegrable g volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hbaseIcc
  have htargetInterval : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 htargetIcc
  have hmajorInterval : IntervalIntegrable (fun s => C * g s) volume 0 T :=
    hbaseInterval.const_mul C
  have hpointwiseMajor : ∀ s ∈ Set.Icc (0 : ℝ) T, f s ≤ C * g s := hcomp
  have htargetMajorIntegral : (∫ s in (0 : ℝ)..T, f s) ≤
      ∫ s in (0 : ℝ)..T, C * g s :=
    intervalIntegral.integral_mono_on hT htargetInterval hmajorInterval hpointwiseMajor
  have hscaledIntegral : (∫ s in (0 : ℝ)..T, C * g s) ≤ C / p := by
    rw [intervalIntegral.integral_const_mul]
    have hbaseIntervalBound : (∫ s in (0 : ℝ)..T, g s) ≤ 1 / p := by
      rw [intervalIntegral.integral_of_le hT]
      exact le_trans hIocBound hbaseIntegralBound
    calc
      C * (∫ s in (0 : ℝ)..T, g s) ≤ C * (1 / p) := mul_le_mul_of_nonneg_left hbaseIntervalBound hC_nonneg
      _ = C / p := by ring
  have hfinal : C / p ≤ 2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ)^k := by
    have hratio2' : 1 / p ≤ 2 := hratio.trans (le_of_lt hratio2)
    calc
      C / p = C * (1 / p) := by ring
      _ ≤ C * 2 := mul_le_mul_of_nonneg_left hratio2' hC_nonneg
      _ = 2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ)^k := by
        dsimp [C]
        ring
  refine ⟨htargetIcc, ?_, hfinal⟩
  exact le_trans htargetMajorIntegral hscaledIntegral

end ThLean.W.S528

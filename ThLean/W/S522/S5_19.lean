module

public import ThLean.BP.S5.Identification

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S522
open ThresholdFoundations
open ThLean.BP.S5

private theorem uniformProb_nonneg {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProb P := by
  unfold uniformProb uniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro a ha
    unfold indicator
    split_ifs <;> norm_num
  · exact Nat.cast_nonneg _

private theorem uniformProb_le_one {A : Type*} [Fintype A] (P : A → Prop) :
    uniformProb P ≤ 1 := by
  unfold uniformProb uniformMean
  by_cases hA : Fintype.card A = 0
  · haveI : IsEmpty A := Fintype.card_eq_zero_iff.mp hA
    simp [hA, indicator]
  · have hcard : 0 < (Fintype.card A : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hA
    rw [div_le_one hcard]
    calc
      (∑ a, indicator (P a)) ≤ ∑ a, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          unfold indicator
          split_ifs <;> norm_num
      _ = (Fintype.card A : ℝ) := by simp

private theorem uniformProb_mono {A : Type*} [Fintype A] {P Q : A → Prop}
    (hPQ : ∀ a, P a → Q a) : uniformProb P ≤ uniformProb Q := by
  unfold uniformProb uniformMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro a ha
  by_cases hp : P a
  · have hq := hPQ a hp
    simp [indicator, hp, hq]
  · unfold indicator
    split_ifs <;> norm_num

private theorem uniformMean_mono {A : Type*} [Fintype A] {f g : A → ℝ}
    (hfg : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun a _ => hfg a

private theorem uniformMean_bounds {A : Type*} [Fintype A] (f : A → ℝ)
    (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 := by
  unfold uniformMean
  by_cases hA : Fintype.card A = 0
  · haveI : IsEmpty A := Fintype.card_eq_zero_iff.mp hA
    simp [hA]
  · have hcard : 0 < (Fintype.card A : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hA
    constructor
    · apply div_nonneg
      · exact Finset.sum_nonneg fun a _ => h0 a
      · exact Nat.cast_nonneg _
    · rw [div_le_one hcard]
      calc
        (∑ a, f a) ≤ ∑ a, (1 : ℝ) := Finset.sum_le_sum fun a _ => h1 a
        _ = (Fintype.card A : ℝ) := by simp

private theorem poissonMixture_measurable_extend
    (hE01 : ThLean.BP.S5.S5_E01Statement)
    (b : ℕ → ℝ) (hb : ∀ m, 0 ≤ b m ∧ b m ≤ 1) :
    Measurable (fun t : ℝ => poissonMixture (max t 0) b) := by
  let w : ℕ → ℝ → ℝ≥0∞ := fun m t =>
    ENNReal.ofReal (poissonWeight (max t 0) m * b m)
  have hw : ∀ m, Measurable (w m) := by
    intro m
    have hmax : Continuous (fun t : ℝ => max t 0) :=
      continuous_max.comp (continuous_id.prodMk continuous_const)
    have hc : Continuous (fun t : ℝ =>
        poissonWeight (max t 0) m * b m) :=
      ((hE01.2 m).comp hmax).mul continuous_const
    exact ENNReal.measurable_ofReal.comp hc.measurable
  have htsum : Measurable (fun t : ℝ => ∑' m, w m t) :=
    Measurable.ennreal_tsum hw
  have hreal : (fun t : ℝ => poissonMixture (max t 0) b) =
      (fun t => ENNReal.toReal (∑' m, w m t)) := by
    funext t
    let z := max t 0
    have hz : 0 ≤ z := le_max_right _ _
    rcases (hE01.1 z hz).2.2.2 1 b (by norm_num) hb with
      ⟨hs, hmix_nonneg, hmix_le⟩
    have hterms : ∀ m, 0 ≤ poissonWeight z m * b m := by
      intro m
      exact mul_nonneg ((hE01.1 z hz).1 m).1 (hb m).1
    have hsum := ENNReal.ofReal_tsum_of_nonneg hterms hs
    have hsum' : ENNReal.ofReal (poissonMixture (max t 0) b) =
        ∑' m, w m t := by
      simpa [w, poissonMixture] using hsum
    change poissonMixture (max t 0) b = (∑' m, w m t).toReal
    rw [← hsum']
    exact (ENNReal.toReal_ofReal hmix_nonneg).symm
  rw [hreal]
  exact htsum.ennreal_toReal

private theorem poissonGraphMean_measurable_extend
    (hE01 : ThLean.BP.S5.S5_E01Statement)
    {V : Type*} [Fintype V] (f : MGraph V → ℝ)
    (h0 : ∀ G, 0 ≤ f G) (h1 : ∀ G, f G ≤ 1) :
    Measurable (fun t : ℝ => poissonGraphMean (max t 0) f) := by
  have hb : ∀ m, 0 ≤ uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)) ∧
      uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)) ≤ 1 := by
    intro m
    apply uniformMean_bounds
    · intro x
      exact h0 _
    · intro x
      exact h1 _
  change Measurable (fun t : ℝ => poissonMixture (max t 0)
    (fun m => uniformMean (fun x : EdgeTuple V m => f (tupleGraph x))))
  exact poissonMixture_measurable_extend hE01
    (fun m => uniformMean (fun x : EdgeTuple V m => f (tupleGraph x))) hb

private theorem poissonGraphMean_nonneg_of_graph_bounds
    (hE01 : ThLean.BP.S5.S5_E01Statement)
    {V : Type*} [Fintype V] (t : ℝ) (ht : 0 ≤ t) (f : MGraph V → ℝ)
    (h0 : ∀ G, 0 ≤ f G) (h1 : ∀ G, f G ≤ 1) :
    0 ≤ poissonGraphMean t f := by
  change 0 ≤ poissonMixture t
    (fun m => uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)))
  have hb : ∀ m, 0 ≤ uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)) ∧
      uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)) ≤ 1 := by
    intro m
    apply uniformMean_bounds
    · intro x
      exact h0 _
    · intro x
      exact h1 _
  exact (hE01.1 t ht).2.2.2 1 _ (by norm_num) hb |>.2.1

private theorem poissonGraphMean_mono_of_graph_bounds
    (hE01 : ThLean.BP.S5.S5_E01Statement)
    {V : Type*} [Fintype V] (t : ℝ) (ht : 0 ≤ t)
    (f g : MGraph V → ℝ)
    (hf0 : ∀ G, 0 ≤ f G) (hf1 : ∀ G, f G ≤ 1)
    (hg0 : ∀ G, 0 ≤ g G) (hg1 : ∀ G, g G ≤ 1)
    (hfg : ∀ G, f G ≤ g G) :
    poissonGraphMean t f ≤ poissonGraphMean t g := by
  change poissonMixture t
      (fun m => uniformMean (fun x : EdgeTuple V m => f (tupleGraph x))) ≤
    poissonMixture t
      (fun m => uniformMean (fun x : EdgeTuple V m => g (tupleGraph x)))
  have hfb : ∀ m, 0 ≤ uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)) ∧
      uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)) ≤ 1 := by
    intro m
    apply uniformMean_bounds
    · intro x
      exact hf0 _
    · intro x
      exact hf1 _
  have hgb : ∀ m, 0 ≤ uniformMean (fun x : EdgeTuple V m => g (tupleGraph x)) ∧
      uniformMean (fun x : EdgeTuple V m => g (tupleGraph x)) ≤ 1 := by
    intro m
    apply uniformMean_bounds
    · intro x
      exact hg0 _
    · intro x
      exact hg1 _
  have hs := hE01.1 t ht
  have hfs : Summable (fun m => poissonWeight t m *
      uniformMean (fun x : EdgeTuple V m => f (tupleGraph x))) :=
    (hs.2.2.2 1 _ (by norm_num) hfb).1
  have hgs : Summable (fun m => poissonWeight t m *
      uniformMean (fun x : EdgeTuple V m => g (tupleGraph x))) :=
    (hs.2.2.2 1 _ (by norm_num) hgb).1
  apply hfs.tsum_le_tsum
  · intro m
    exact mul_le_mul_of_nonneg_left
      (uniformMean_mono fun x => hfg (tupleGraph x)) (hs.1 m).1
  · exact hgs

private theorem poissonGraphMean_colorable_eq_survival
    {V : Type*} [Fintype V] (q : ℕ) (t : ℝ) :
    poissonGraphMean t (fun G : MGraph V => indicator (Colorable q G)) =
      poissonMixture t (fun m => processSurvival (V := V) q m) := by
  change poissonMixture t
      (fun m => uniformMean (fun x : EdgeTuple V m =>
        indicator (Colorable q (tupleGraph x)))) = _
  congr 1
  funext m
  simp [processSurvival, survival, uniformProb, uniformMean]

private theorem poissonGraphMean_eq_mixture
    {V : Type*} [Fintype V] (t : ℝ) (f : MGraph V → ℝ) :
    poissonGraphMean t f = poissonMixture t
      (fun m => uniformMean (fun x : EdgeTuple V m => f (tupleGraph x))) := rfl

theorem S5_19Statement_of_deps
    (h18 : ThLean.BP.S5.S5_18Statement)
    (hE01 : ThLean.BP.S5.S5_E01Statement) :
    ThLean.BP.S5.S5_19Statement := by
  intro q N D hq hN hD hDN
  have hqR : 0 < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hq)
  have hqOne : 1 < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hq)
  have hlog : 0 < Real.log (q : ℝ) :=
    Real.log_pos hqOne
  have hcap_nonneg : 0 ≤ lowTimeCap q N := by
    unfold lowTimeCap
    positivity
  let c : ℝ := 1 / (2 * (q : ℝ))
  have hrate_pos : 0 < c := by
    dsimp [c]
    positivity
  have hrate_lt_one : c < 1 := by
    dsimp [c]
    rw [div_lt_iff₀ (by positivity : 0 < 2 * (q : ℝ))]
    nlinarith
  have hsurv := h18 (V := Fin N) q hq (by simpa using hN)
  have hsurv_nonneg (m : ℕ) : 0 ≤ processSurvival (V := Fin N) q m := by
    unfold processSurvival survival uniformProb uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x hx
      unfold indicator
      split_ifs <;> norm_num
    · exact Nat.cast_nonneg _
  let fdisc : MGraph (Fin N) → ℝ := identificationFailureProbability q D
  let fcolor : MGraph (Fin N) → ℝ := fun G => indicator (Colorable q G)
  have hdisc0 : ∀ G, 0 ≤ fdisc G := by
    intro G
    exact uniformProb_nonneg _
  have hdisc1 : ∀ G, fdisc G ≤ 1 := by
    intro G
    exact uniformProb_le_one _
  have hcolor0 : ∀ G, 0 ≤ fcolor G := by
    intro G
    unfold fcolor indicator
    split_ifs <;> norm_num
  have hcolor1 : ∀ G, fcolor G ≤ 1 := by
    intro G
    unfold fcolor indicator
    split_ifs <;> norm_num
  have hfailure_le_color : ∀ G, fdisc G ≤ fcolor G := by
    intro G
    by_cases hc : Colorable q G
    · simp [fdisc, fcolor, identificationFailureProbability, indicator, hc]
      exact uniformProb_le_one _
    · simp [fdisc, fcolor, identificationFailureProbability, uniformProb,
        uniformMean, indicator, hc]
  have hmain : ∀ s : ℝ, 0 ≤ s →
      0 ≤ discrepancy q N D s ∧
      discrepancy q N D s ≤ poissonGraphMean s
        (fun G : MGraph (Fin N) => indicator (Colorable q G)) ∧
      poissonGraphMean s (fun G : MGraph (Fin N) => indicator (Colorable q G)) ≤
        (q : ℝ)^N * Real.exp (-s / (2 * q)) := by
    intro s hs
    have hsE := hE01.1 s hs
    have hweight_nonneg : ∀ m, 0 ≤ poissonWeight s m := fun m => (hsE.1 m).1
    have hdisc_nonneg : 0 ≤ discrepancy q N D s := by
      change 0 ≤ poissonGraphMean s fdisc
      exact poissonGraphMean_nonneg_of_graph_bounds hE01 s hs fdisc hdisc0 hdisc1
    have hdisc_color : discrepancy q N D s ≤
        poissonGraphMean s (fun G : MGraph (Fin N) => indicator (Colorable q G)) := by
      change poissonGraphMean s fdisc ≤ poissonGraphMean s fcolor
      exact poissonGraphMean_mono_of_graph_bounds hE01 s hs fdisc fcolor
        hdisc0 hdisc1 hcolor0 hcolor1 hfailure_le_color
    let a : ℝ := 1 - 1 / (2 * (q : ℝ))
    have ha : 0 ≤ a := by
      dsimp [a]
      have : 1 / (2 * (q : ℝ)) < 1 := by simpa [c] using hrate_lt_one
      linarith
    have hgen := hsE.2.2.1 a ha
    have hscaled : Summable (fun m => (q : ℝ)^N *
        (poissonWeight s m * a^m)) := (hgen.mul_left ((q : ℝ)^N)).summable
    have hsurv_sum : Summable (fun m => poissonWeight s m *
        processSurvival (V := Fin N) q m) := by
      refine Summable.of_nonneg_of_le
        (fun m => mul_nonneg (hweight_nonneg m) (hsurv_nonneg m))
        (fun m => ?_) hscaled
      have hsbound : processSurvival (V := Fin N) q m ≤
          (q : ℝ)^N * a^m := by
        simpa [a] using hsurv.2 m
      calc
        poissonWeight s m * processSurvival (V := Fin N) q m ≤
            poissonWeight s m * ((q : ℝ)^N * a^m) :=
          mul_le_mul_of_nonneg_left hsbound (hweight_nonneg m)
        _ = (q : ℝ)^N * (poissonWeight s m * a^m) := by ring
    have hcolor_surv := poissonGraphMean_colorable_eq_survival (V := Fin N) q s
    have hmixture_le : poissonMixture s (fun m => processSurvival (V := Fin N) q m) ≤
        (q : ℝ)^N * Real.exp (-s / (2 * (q : ℝ))) := by
      calc
        poissonMixture s (fun m => processSurvival (V := Fin N) q m) =
            ∑' m, poissonWeight s m * processSurvival (V := Fin N) q m := rfl
        _ ≤ ∑' m, (q : ℝ)^N * (poissonWeight s m * a^m) :=
          hsurv_sum.tsum_le_tsum (fun m => by
            have hsbound : processSurvival (V := Fin N) q m ≤
                (q : ℝ)^N * a^m := by
              simpa [a] using hsurv.2 m
            calc
              poissonWeight s m * processSurvival (V := Fin N) q m ≤
                  poissonWeight s m * ((q : ℝ)^N * a^m) :=
                mul_le_mul_of_nonneg_left hsbound (hweight_nonneg m)
              _ = (q : ℝ)^N * (poissonWeight s m * a^m) := by ring) hscaled
        _ = (q : ℝ)^N * Real.exp (s * (a - 1)) :=
          (hgen.mul_left ((q : ℝ)^N)).tsum_eq
        _ = (q : ℝ)^N * Real.exp (-s / (2 * (q : ℝ))) := by
          congr 1
          dsimp [a]
          field_simp
          ring
    refine ⟨hdisc_nonneg, hdisc_color, ?_⟩
    rw [hcolor_surv]
    exact hmixture_le
  have hdiscMeas : Measurable (fun s : ℝ =>
      poissonGraphMean (max s 0) fdisc) :=
    poissonGraphMean_measurable_extend hE01 fdisc hdisc0 hdisc1
  let cap := lowTimeCap q N
  have hExpIoi : IntegrableOn (fun s : ℝ => Real.exp ((-c) * s)) (Set.Ioi cap) :=
    integrableOn_exp_mul_Ioi (by linarith) cap
  have hExpIci : IntegrableOn (fun s : ℝ => Real.exp (-c * s)) (Set.Ici cap) := by
    exact (integrableOn_Ici_iff_integrableOn_Ioi).2 hExpIoi
  have hExpIntegral :
      (∫ s in Set.Ici cap, Real.exp (-c * s)) = Real.exp (-c * cap) / c := by
    rw [integral_Ici_eq_integral_Ioi]
    calc
      (∫ s in Set.Ioi cap, Real.exp (-c * s)) =
          -Real.exp (-c * cap) / (-c) :=
        integral_exp_mul_Ioi (a := -c) (by linarith) cap
      _ = Real.exp (-c * cap) / c := by
        field_simp [ne_of_gt hrate_pos]
  have hmajorInt : IntegrableOn (fun s : ℝ => (q : ℝ)^N * Real.exp (-c * s))
      (Set.Ici cap) := by
    change Integrable (fun s : ℝ => (q : ℝ)^N * Real.exp (-c * s))
      (volume.restrict (Set.Ici cap))
    exact hExpIci.integrable.const_mul ((q : ℝ)^N)
  have hdiscSubMeas : Measurable (fun x : Set.Ici cap => discrepancy q N D x.val) := by
    have hm : Measurable (fun x : Set.Ici cap =>
        poissonGraphMean (max x.val 0) fdisc) :=
      hdiscMeas.comp measurable_subtype_coe
    have hfun : (fun x : Set.Ici cap => discrepancy q N D x.val) =
        (fun x => poissonGraphMean (max x.val 0) fdisc) := by
      funext x
      simp [discrepancy, fdisc, max_eq_left (le_trans hcap_nonneg x.property)]
    rw [hfun]
    exact hm
  have hdiscSubInt : Integrable
      (fun x : Set.Ici cap => discrepancy q N D x.val)
      (volume.comap (fun x : Set.Ici cap => (x : ℝ))) := by
    apply Integrable.mono' (integrableOn_iff_comap_subtypeVal measurableSet_Ici |>.mp hmajorInt)
      hdiscSubMeas.aestronglyMeasurable
    filter_upwards [] with x
    have hx0 : 0 ≤ x.val := le_trans hcap_nonneg x.property
    have hbound := hmain x.val hx0
    have hExpEq : Real.exp (-c * x.val) =
        Real.exp (-x.val / (2 * (q : ℝ))) := by
      congr 1
      dsimp [c]
      ring
    change ‖discrepancy q N D x.val‖ ≤
      (q : ℝ)^N * Real.exp (-c * x.val)
    rw [Real.norm_eq_abs, abs_of_nonneg hbound.1]
    apply le_trans hbound.2.1
    rw [hExpEq]
    exact hbound.2.2
  have hdiscInt : IntegrableOn (discrepancy q N D) (Set.Ici cap) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mpr hdiscSubInt
  have hIntegralLe :
      (∫ s in Set.Ici cap, discrepancy q N D s) ≤
      ∫ s in Set.Ici cap, (q : ℝ)^N * Real.exp (-c * s) := by
    apply setIntegral_mono_on hdiscInt hmajorInt measurableSet_Ici
    intro s hs
    have hs0 : 0 ≤ s := le_trans hcap_nonneg hs
    have hb := hmain s hs0
    have hExpEq : Real.exp (-c * s) = Real.exp (-s / (2 * (q : ℝ))) := by
      congr 1
      dsimp [c]
      ring
    rw [hExpEq]
    exact le_trans hb.2.1 hb.2.2
  have hmajorValue :
      (∫ s in Set.Ici cap, (q : ℝ)^N * Real.exp (-c * s)) = 2 * (q : ℝ) := by
    rw [integral_const_mul, hExpIntegral]
    have hpowpos : 0 < (q : ℝ)^N := pow_pos hqR _
    have hlogpow : Real.log ((q : ℝ)^N) = (N : ℝ) * Real.log (q : ℝ) :=
      Real.log_pow (q : ℝ) N
    have hexpArg : -c * cap = -Real.log ((q : ℝ)^N) := by
      dsimp [c, cap, lowTimeCap]
      rw [hlogpow]
      field_simp [ne_of_gt hqR] <;> ring
    rw [hexpArg, Real.exp_neg, Real.exp_log hpowpos]
    dsimp [c]
    field_simp [ne_of_gt hqR] <;> ring
  have hmajorIntTarget : IntegrableOn
      (fun s : ℝ => (q : ℝ)^N * Real.exp (-s / (2 * (q : ℝ))))
      (Set.Ici cap) := by
    have hfun : (fun s : ℝ => (q : ℝ)^N * Real.exp (-s / (2 * (q : ℝ)))) =
        (fun s => (q : ℝ)^N * Real.exp (-c * s)) := by
      funext s
      congr 2
      dsimp [c]
      ring
    rw [hfun]
    exact hmajorInt
  refine ⟨hmain, ?_, hdiscInt, ?_⟩
  · simpa [cap] using hmajorIntTarget
  · exact hIntegralLe.trans_eq hmajorValue

example (h18 : ThLean.BP.S5.S5_18Statement)
    (hE01 : ThLean.BP.S5.S5_E01Statement) :
    ThLean.BP.S5.S5_19Statement :=
  S5_19Statement_of_deps h18 hE01

end ThLean.W.S522

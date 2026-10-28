import ThLean.BP.S5.Occupation

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S543
open ThresholdFoundations ThLean.BP.S5

private lemma indicator_unit_interval (P : Prop) :
    0 ≤ indicator P ∧ indicator P ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

theorem S5_33BStatement_of_deps
    (h32 : ThLean.BP.S5.S5_32Statement)
    (h33a : ThLean.BP.S5.S5_33AStatement)
    (h08b : ThLean.BP.S5.S5_08BStatement)
    (h08c : ThLean.BP.S5.S5_08CStatement)
    (hE01 : ThLean.BP.S5.S5_E01Statement) :
    ThLean.BP.S5.S5_33BStatement := by
  intro q n D hq hn hD hDn a
  let f : MGraph (Fin n) → ℝ := fun G => indicator (rootEvent q D a G)
  let den : ℝ := ((n.choose 2 : ℕ) : ℝ)
  have hn2 : 2 ≤ n := by omega
  have hnN : 1 ≤ n - 1 := by omega
  have hden : 0 < den := by
    dsimp [den]
    exact_mod_cast (Nat.choose_pos (show 2 ≤ n by omega))
  have hrate_nonneg :
      ∀ e : Sym2 (Fin n),
        0 ≤ if ∃ v : Fin n, e = s(v, v) then 0 else 1 / den := by
    intro e
    split_ifs <;> positivity
  have hrate_eq (t : Set.Ici (0 : ℝ)) (e : Sym2 (Fin n)) :
      (if ∃ v : Fin n, e = s(v, v) then 0 else 1 / den) * t.val =
        perPairRate (t.val / den) e := by
    by_cases he : ∃ v : Fin n, e = s(v, v)
    · simp [perPairRate, he]
    · simp [perPairRate, he, den]
      ring
  have hf_bound : ∃ C : ℝ, ∀ G : MGraph (Fin n), |f G| ≤ C := by
    refine ⟨1, ?_⟩
    intro G
    dsimp [f]
    unfold indicator
    split_ifs <;> norm_num
  have hcount_meas : Measurable (fun t : Set.Ici (0 : ℝ) =>
      countMean (t.val / den) f) := by
    let rate : Sym2 (Fin n) → ℝ := fun e =>
      if ∃ v : Fin n, e = s(v, v) then 0 else 1 / den
    have hrate : ∀ e, 0 ≤ rate e := by
      intro e
      exact hrate_nonneg e
    have hm := h08c (Sym2 (Fin n)) rate hrate f hf_bound
    have heq : (fun t : Set.Ici (0 : ℝ) => countMean (t.val / den) f) =
        fun t => ∑' G : Sym2 (Fin n) → ℕ,
          (∏ e, poissonWeight (rate e * t.val) (G e)) * f G := by
      funext t
      dsimp [countMean, independentPoissonGraphMean]
      apply tsum_congr
      intro G
      congr 1
      apply Finset.prod_congr rfl
      intro e he
      dsimp [rate]
      rw [← hrate_eq t e]
    intro s hs
    rw [heq]
    exact hm hs
  have hroot_meas : Measurable (fun t : Set.Ici (0 : ℝ) =>
      rootProbability q D a t.val) := by
    have heq : (fun t : Set.Ici (0 : ℝ) => rootProbability q D a t.val) =
        fun t => countMean (t.val / den) f := by
      funext t
      dsimp [rootProbability, f]
      simpa [den] using h08b (Fin n) (by simpa using hn2) t.val t.property
        (fun G => indicator (rootEvent q D a G)) hf_bound
    intro s hs
    rw [heq]
    exact hcount_meas hs
  have hroot_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ rootProbability q D a t := by
    intro t ht
    unfold rootProbability poissonGraphMean poissonMixture
    apply tsum_nonneg
    intro m
    apply mul_nonneg
    · exact ((hE01.1 t ht).1 m).1
    · unfold uniformMean
      apply div_nonneg
      · exact Finset.sum_nonneg fun x _ => (indicator_unit_interval _).1
      · positivity
  have hdom : ∀ t : ℝ, 0 ≤ t →
      rootProbability q D a t ≤ nmTime q (n - 1) D ((((n : ℝ) - 2) / n) * t) := by
    intro t ht
    exact ((h32 q n D hq (by omega) a t ht).1).trans
      (h32 q n D hq (by omega) a t ht).2
  have hnmInt := (h33a q n D hq hn hD hDn).2.2.1
  have hroot_sm : AEStronglyMeasurable (rootProbability q D a)
      (volume.restrict (Set.Ici 0)) := by
    obtain ⟨g, hg, hgeq⟩ :=
      (MeasurableEmbedding.subtype_coe measurableSet_Ici).exists_measurable_extend
        hroot_meas (fun _ : ℝ => (⟨0⟩ : Nonempty ℝ))
    have heq : g =ᵐ[volume.restrict (Set.Ici 0)] rootProbability q D a := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have h := congrFun hgeq ⟨t, ht⟩
      simpa using h
    exact (hg.aestronglyMeasurable.mono_measure Measure.restrict_le_self).congr heq
  have hrootInt : IntegrableOn (rootProbability q D a) (Set.Ici 0) := by
    apply Integrable.mono_nonneg hnmInt.integrable hroot_sm
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact hroot_nonneg t ht
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact hdom t ht
  refine ⟨hrootInt, ?_⟩
  apply setIntegral_mono_of_nonneg
  · intro t ht
    exact hroot_nonneg t ht
  · intro t ht
    exact hdom t ht
  · exact hnmInt

end ThLean.W.S543

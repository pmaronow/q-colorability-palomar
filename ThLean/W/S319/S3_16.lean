import ThLean.BP.S3.Terminal

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S319

open ThresholdFoundations
open ThLean.BP.S3
universe u

private theorem uniformMean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [Equiv.sum_comp e]
  simp [Fintype.card_congr e]

private theorem uniformMean_prod {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a, b))) := by
  classical
  unfold uniformMean
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    have hp : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ‹Nonempty A›
    exact_mod_cast (Nat.ne_of_gt hp)
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    have hp : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ‹Nonempty B›
    exact_mod_cast (Nat.ne_of_gt hp)
  field_simp [hA, hB]
  rw [← Finset.sum_div]
  field_simp [hB]

private theorem uniformMean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  unfold uniformMean
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    have hp : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ‹Nonempty A›
    exact_mod_cast (Nat.ne_of_gt hp)
  field_simp

private theorem tupleGraph_snoc_apply {V : Type*} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (e f : Pair V) :
    tupleGraph (Fin.snoc x e) f.val =
      tupleGraph x f.val + if e.val = f.val then 1 else 0 := by
  classical
  simp only [tupleGraph, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

private theorem tupleGraph_snoc_mono {V : Type*} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (e : Pair V) (f : Sym2 V) :
    tupleGraph x f ≤ tupleGraph (Fin.snoc x e) f := by
  classical
  by_cases h : ∃ p : Pair V, p.val = f
  · obtain ⟨p, rfl⟩ := h
    rw [tupleGraph_snoc_apply]
    omega
  · have hf : ∀ p : Pair V, p.val ≠ f := fun p hp => h ⟨p, hp⟩
    simp [tupleGraph, Finset.card_eq_zero.mpr, hf]

private theorem pair_nonempty {V : Type*} [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  have hcard : 1 < Fintype.card V := by omega
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.mp hcard
  refine ⟨⟨s(u, v), ?_⟩⟩
  intro w hw
  have h := Sym2.eq_iff.mp hw
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact huv (hu.trans hv.symm)
  · exact huv (hu.trans hv.symm)

private def tupleSnocEquiv {V : Type*} {m : ℕ} :
    Pair V × EdgeTuple V m ≃ EdgeTuple V (m+1) :=
  Fin.snocEquiv (fun _ : Fin (m+1) => Pair V)

private theorem uniformMean_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun x => f x - g x) = uniformMean f - uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_sub_distrib, sub_div]

private theorem survival_step_event {V : Type*} [Fintype V] (q m : ℕ)
    (hV : 2 ≤ Fintype.card V) :
    hittingMass (V := V) q m =
      uniformMean (fun y : EdgeTuple V (m+1) =>
        indicator (Colorable q (tupleGraph (initTuple y)) ∧
          ¬ Colorable q (tupleGraph y))) := by
  classical
  letI : Nonempty (Pair V) := pair_nonempty hV
  have hm : processSurvival (V := V) q m =
      uniformMean (fun p : Pair V × EdgeTuple V m =>
        indicator (Colorable q (tupleGraph p.2))) := by
    rw [uniformMean_prod]
    simp [processSurvival, survival, uniformProb, uniformMean, zero_add,
      uniformMean_const]
  have hm1 : processSurvival (V := V) q (m+1) =
      uniformMean (fun p : Pair V × EdgeTuple V m =>
        indicator (Colorable q (tupleGraph (Fin.snoc p.2 p.1)))) := by
    unfold processSurvival survival uniformProb
    rw [← uniformMean_equiv (tupleSnocEquiv (V := V) (m := m))]
    apply congrArg uniformMean
    funext p
    dsimp [tupleSnocEquiv, Fin.snocEquiv]
    simp [zero_add]
  unfold hittingMass
  rw [hm, hm1, ← uniformMean_sub]
  have hpoint : ∀ p : Pair V × EdgeTuple V m,
      indicator (Colorable q (tupleGraph p.2)) -
        indicator (Colorable q (tupleGraph (Fin.snoc p.2 p.1))) =
      indicator (Colorable q (tupleGraph p.2) ∧
        ¬ Colorable q (tupleGraph (Fin.snoc p.2 p.1))) := by
    intro p
    have hmono : Colorable q (tupleGraph (Fin.snoc p.2 p.1)) →
        Colorable q (tupleGraph p.2) := by
      intro hc
      rcases hc with ⟨σ, hσ⟩
      refine ⟨σ, ?_⟩
      intro u v huv
      apply hσ
      exact lt_of_lt_of_le huv (tupleGraph_snoc_mono p.2 p.1 (s(u,v)))
    by_cases hc : Colorable q (tupleGraph p.2)
    · by_cases hf : Colorable q (tupleGraph (Fin.snoc p.2 p.1))
      · simp [indicator, hc, hf]
      · simp [indicator, hc, hf]
    · have hf : ¬ Colorable q (tupleGraph (Fin.snoc p.2 p.1)) := by
        intro hf
        exact hc (hmono hf)
      simp [indicator, hc, hf]
  rw [← uniformMean_equiv (tupleSnocEquiv (V := V) (m := m))
    (fun y : EdgeTuple V (m+1) => indicator (Colorable q (tupleGraph (initTuple y)) ∧
      ¬ Colorable q (tupleGraph y)))]
  apply congrArg uniformMean
  funext p
  change indicator (Colorable q (tupleGraph p.2)) -
      indicator (Colorable q (tupleGraph (Fin.snoc p.2 p.1))) =
    indicator (Colorable q (tupleGraph (initTuple (Fin.snoc p.2 p.1))) ∧
      ¬ Colorable q (tupleGraph (Fin.snoc p.2 p.1)))
  have hinit : initTuple (Fin.snoc p.2 p.1) = p.2 := by
    funext i
    simp [initTuple]
  rw [hinit]
  exact hpoint p

private theorem uniformMeanENN_ofReal_toReal {A : Type*} [Fintype A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (uniformMeanENN (fun a => ENNReal.ofReal (f a))).toReal = uniformMean f := by
  unfold uniformMeanENN
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_sum (by intro a ha; exact ENNReal.ofReal_ne_top)]
  simp [uniformMean, hf]

private theorem uniformMean_nonneg {A : Type*} [Fintype A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  unfold uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg fun a ha => hf a
  · exact Nat.cast_nonneg _

private theorem kappa_nonneg {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V) :
    0 ≤ kappa q G := by
  unfold kappa uniformProb uniformMean indicator
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro e he
    split_ifs <;> norm_num
  · exact Nat.cast_nonneg _

private theorem hazard_weight_eq {V : Type u} [Fintype V] (q m : ℕ)
    (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V)
    (h15 : ThLean.BP.S3.S3_15Statement.{u})
    (z : EdgeTuple V m → ℝ) (hz : ∀ x, 0 ≤ z x) :
    uniformMean (fun x : EdgeTuple V m => z x * kappa q (tupleGraph x)) =
      uniformMean (fun y : EdgeTuple V (m+1) =>
        z (initTuple y) * indicator (Colorable q (tupleGraph (initTuple y)) ∧
          ¬ Colorable q (tupleGraph y))) := by
  classical
  let zENN : EdgeTuple V m → ℝ≥0∞ := fun x => ENNReal.ofReal (z x)
  have hENN := h15 V q hq hV m zENN
  have hleft : uniformMeanENN
      (fun y : EdgeTuple V (m+1) => zENN (initTuple y) *
        if Colorable q (tupleGraph (initTuple y)) ∧ ¬ Colorable q (tupleGraph y)
        then 1 else 0) =
      uniformMeanENN (fun y : EdgeTuple V (m+1) => ENNReal.ofReal
        (z (initTuple y) * indicator (Colorable q (tupleGraph (initTuple y)) ∧
          ¬ Colorable q (tupleGraph y)))) := by
    apply congrArg uniformMeanENN
    funext y
    by_cases he : Colorable q (tupleGraph (initTuple y)) ∧
        ¬ Colorable q (tupleGraph y)
    · simp [zENN, indicator, he, ENNReal.ofReal_mul, hz]
    · simp [zENN, indicator, he]
  have hright : uniformMeanENN
      (fun x : EdgeTuple V m => zENN x * ENNReal.ofReal (kappa q (tupleGraph x))) =
      uniformMeanENN (fun x : EdgeTuple V m => ENNReal.ofReal
        (z x * kappa q (tupleGraph x))) := by
    apply congrArg uniformMeanENN
    funext x
    simp [zENN, ENNReal.ofReal_mul, hz, kappa_nonneg]
  have ht := congrArg ENNReal.toReal hENN
  rw [hleft, hright] at ht
  rw [uniformMeanENN_ofReal_toReal] at ht
  · rw [uniformMeanENN_ofReal_toReal] at ht
    · exact ht.symm
    · intro x
      exact mul_nonneg (hz x) (kappa_nonneg q (tupleGraph x))
  · intro y
    apply mul_nonneg (hz (initTuple y))
    by_cases he : Colorable q (tupleGraph (initTuple y)) ∧ ¬ Colorable q (tupleGraph y)
    · simp [indicator, he]
    · simp [indicator, he]

private theorem uniformMean_le {A : Type*} [Fintype A] [Nonempty A]
    (f g : A → ℝ) (hfg : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun a ha => hfg a
  · exact Nat.cast_nonneg _

private theorem survival_nonneg {V : Type*} [Fintype V] (q m : ℕ) :
    0 ≤ processSurvival (V := V) q m := by
  unfold processSurvival survival uniformProb uniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro x hx
    by_cases h : Colorable q (tupleGraph x)
    · simp [indicator, h]
    · simp [indicator, h]
  · exact Nat.cast_nonneg _

private theorem processSurvival_zero {V : Type*} [Fintype V] (q : ℕ)
    (hq : 2 ≤ q) : processSurvival (V := V) q 0 = 1 := by
  classical
  letI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  simp [processSurvival, survival, uniformProb, uniformMean, indicator,
    Colorable, IsColoring, tupleGraph]

private theorem hittingMass_nonneg_of_antitone {V : Type*} [Fintype V]
    (q m : ℕ) (hanti : Antitone (processSurvival (V := V) q)) :
    0 ≤ hittingMass (V := V) q m := by
  unfold hittingMass
  exact sub_nonneg.mpr (hanti (by omega))

private theorem hittingMass_summable_formula {V : Type u} [Fintype V]
    (q : ℕ) (hq : 2 ≤ q) (h04 : ThLean.BP.S3.S3_04aStatement.{u})
    (hV : 2 ≤ Fintype.card V) :
    Summable (fun m => hittingMass (V := V) q m) ∧
      (∑' m, hittingMass (V := V) q m) =
        1 - infiniteHittingProbability (V := V) q := by
  let s : ℕ → ℝ := processSurvival (V := V) q
  let b : ℕ → ℝ := fun m => hittingMass (V := V) q m
  have hanti : Antitone s := by
    simpa [s] using (h04 V q hq).2.2.2
  have hs0 : s 0 = 1 := by simpa [s] using processSurvival_zero q hq
  have hbnonneg : ∀ m, 0 ≤ b m := by
    intro m
    exact hittingMass_nonneg_of_antitone q m (by simpa [s] using hanti)
  have hrange : ∀ n, (∑ m ∈ Finset.range n, b m) = 1 - s n := by
    intro n
    induction n with
    | zero => simp [hs0]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [b, s]
        unfold hittingMass
        ring
  have hbSummable : Summable b :=
    summable_of_sum_range_le hbnonneg (by
      intro n
      rw [hrange n]
      have hn := survival_nonneg (V := V) q n
      linarith)
  have hbelow : BddBelow (Set.range s) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact survival_nonneg (V := V) q n
  have hlim : Tendsto s atTop (𝓝 (infiniteHittingProbability (V := V) q)) := by
    change Tendsto s atTop (𝓝 (sInf (Set.range s)))
    exact tendsto_atTop_isGLB hanti (isGLB_csInf (Set.range_nonempty s) hbelow)
  have hsumLimit : Tendsto (fun n => ∑ m ∈ Finset.range n, b m) atTop
      (𝓝 (1 - infiniteHittingProbability (V := V) q)) := by
    have h' : Tendsto (fun n => 1 - s n) atTop
        (𝓝 (1 - infiniteHittingProbability (V := V) q)) :=
      tendsto_const_nhds.sub hlim
    have heq : (fun n => ∑ m ∈ Finset.range n, b m) = fun n => 1 - s n :=
      funext hrange
    rw [heq]
    exact h'
  have htsumLimit : Tendsto (fun n => ∑ m ∈ Finset.range n, b m) atTop
      (𝓝 (∑' m, b m)) := hbSummable.hasSum.tendsto_sum_nat
  have hsumEq : (∑' m, b m) = 1 - infiniteHittingProbability (V := V) q :=
    tendsto_nhds_unique htsumLimit hsumLimit
  exact ⟨by simpa [b] using hbSummable, by simpa [b] using hsumEq⟩

theorem S3_16Statement_of_deps
    (h04 : ThLean.BP.S3.S3_04aStatement.{u})
    (h15 : ThLean.BP.S3.S3_15Statement.{u}) :
    ThLean.BP.S3.S3_16Statement.{u} := by
  intro V _ q hq hV J z hz
  dsimp
  letI : Nonempty (Pair V) := pair_nonempty hV
  let a : ℕ → ℝ := fun m => if m ∈ J then
    uniformMean (fun x : EdgeTuple V m => z m x * kappa q (tupleGraph x)) else 0
  let c : ℕ → ℝ := fun m => if m ∈ J then hittingMass (V := V) q m else 0
  have hanti : Antitone (processSurvival (V := V) q) :=
    (h04 V q hq).2.2.2
  have hb := hittingMass_summable_formula q hq h04 hV
  rcases hb with ⟨hbSum, hbFormula⟩
  have hweight : ∀ m ∈ J,
      uniformMean (fun x : EdgeTuple V m => z m x * kappa q (tupleGraph x)) ≤
        hittingMass (V := V) q m := by
    intro m hm
    calc
      uniformMean (fun x : EdgeTuple V m => z m x * kappa q (tupleGraph x)) =
          uniformMean (fun y : EdgeTuple V (m+1) =>
            z m (initTuple y) * indicator
              (Colorable q (tupleGraph (initTuple y)) ∧
                ¬ Colorable q (tupleGraph y))) :=
        hazard_weight_eq q m hq hV h15 (z m) (fun x => (hz m hm x).1)
      _ ≤ uniformMean (fun y : EdgeTuple V (m+1) =>
            indicator (Colorable q (tupleGraph (initTuple y)) ∧
              ¬ Colorable q (tupleGraph y))) := by
        apply uniformMean_le
        intro y
        by_cases hy : Colorable q (tupleGraph (initTuple y)) ∧
            ¬ Colorable q (tupleGraph y)
        · simpa [indicator, hy] using (hz m hm (initTuple y)).2
        · simp [indicator, hy]
      _ = hittingMass (V := V) q m :=
        (survival_step_event q m hV).symm
  have haNonneg : ∀ m, 0 ≤ a m := by
    intro m
    by_cases hm : m ∈ J
    · simp only [a, if_pos hm]
      apply uniformMean_nonneg
      intro x
      exact mul_nonneg (hz m hm x).1 (kappa_nonneg q (tupleGraph x))
    · simp [a, hm]
  have hcNonneg : ∀ m, 0 ≤ c m := by
    intro m
    by_cases hm : m ∈ J
    · simp only [c, if_pos hm]
      exact hittingMass_nonneg_of_antitone q m hanti
    · simp [c, hm]
  have hac : ∀ m, a m ≤ c m := by
    intro m
    by_cases hm : m ∈ J
    · simpa [a, c, hm] using hweight m hm
    · simp [a, c, hm]
  have hcb : ∀ m, c m ≤ hittingMass (V := V) q m := by
    intro m
    by_cases hm : m ∈ J
    · simp [c, hm]
    · simp [c, hm]
      exact hittingMass_nonneg_of_antitone q m hanti
  have hcSum : Summable c := Summable.of_nonneg_of_le hcNonneg hcb hbSum
  have haSum : Summable a := Summable.of_nonneg_of_le haNonneg hac hcSum
  have hsumc : (∑' m, c m) ≤ 1 := by
    calc
      (∑' m, c m) ≤ ∑' m, hittingMass (V := V) q m := hcSum.tsum_le_tsum hcb hbSum
      _ = 1 - infiniteHittingProbability (V := V) q := hbFormula
      _ ≤ 1 := by
        have hinf : 0 ≤ infiniteHittingProbability (V := V) q := by
          unfold infiniteHittingProbability
          apply le_csInf (Set.range_nonempty (processSurvival (V := V) q))
          rintro x ⟨m, rfl⟩
          exact survival_nonneg (V := V) q m
        linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [a] using haSum
  · simpa [a, c] using haSum.tsum_le_tsum hac hcSum
  · simpa [c] using hsumc
  · exact hbFormula

end ThLean.W.S319

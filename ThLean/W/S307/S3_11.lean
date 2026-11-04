module

public import ThLean.BP.S3.Graph

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S307
open ThresholdFoundations
universe u

private theorem noLoop_iff_not_isDiag {α : Type*} [DecidableEq α] (z : Sym2 α) :
    (∀ v : α, z ≠ s(v, v)) ↔ ¬ z.IsDiag := by
  induction z using Sym2.ind with
  | h a b => simp [eq_comm]

private def pairEquivNotDiag (V : Type*) [DecidableEq V] :
    Pair V ≃ {z : Sym2 V // ¬ z.IsDiag} where
  toFun e := ⟨e.val, (noLoop_iff_not_isDiag e.val).mp e.property⟩
  invFun z := ⟨z.val, (noLoop_iff_not_isDiag z.val).mpr z.property⟩
  left_inv := by intro e; cases e; rfl
  right_inv := by intro z; cases z; rfl

private theorem frozenClass_eq {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V)
    (heq : Equivalence (Frozen q G)) {u v : V} (huv : Frozen q G u v) :
    frozenClass q G u = frozenClass q G v := by
  ext w
  simp only [frozenClass, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro huw
    exact heq.trans (heq.symm huv) huw
  · intro hvw
    exact heq.trans huv hvw

private theorem sum_card_family_of_unique {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (s : Finset α) (t : ι → Finset α)
    (ht : ∀ i ∈ I, t i ⊆ s)
    (huniq : ∀ a ∈ s, {i ∈ I | a ∈ t i}.card = 1) :
    (∑ i ∈ I, (t i).card) = s.card := by
  classical
  have hcard (i : ι) (hi : i ∈ I) :
      (t i).card = ∑ a ∈ s, if a ∈ t i then (1 : ℕ) else 0 := by
    calc
      (t i).card = (s.filter fun a => a ∈ t i).card := by
        congr 1
        ext a
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨ht i hi h, h⟩, fun h => h.2⟩
      _ = ∑ a ∈ s, if a ∈ t i then 1 else 0 := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ i ∈ I, (t i).card) = ∑ i ∈ I, ∑ a ∈ s, if a ∈ t i then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hcard i hi
    _ = ∑ a ∈ s, ∑ i ∈ I, if a ∈ t i then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ s, 1 := by
      apply Finset.sum_congr rfl
      intro a ha
      have h := huniq a ha
      calc
        (∑ i ∈ I, if a ∈ t i then (1 : ℕ) else 0) =
            ∑ i ∈ I with a ∈ t i, (1 : ℕ) := by rw [Finset.sum_filter]
        _ = {i ∈ I | a ∈ t i}.card := by rw [Finset.card_eq_sum_ones]
        _ = 1 := h
    _ = s.card := (Finset.card_eq_sum_ones s).symm

private theorem nat_mul_pred_add_self (n : ℕ) (hn : 1 ≤ n) :
    n * (n - 1) + n = n ^ 2 := by
  have hle : n ≤ n * n := by
    calc
      n = n * 1 := by simp
      _ ≤ n * n := Nat.mul_le_mul_left n hn
  calc
    n * (n - 1) + n = (n * n - n) + n := by
      rw [Nat.mul_sub_left_distrib]
      simp
    _ = n * n := Nat.sub_add_cancel hle
    _ = n ^ 2 := by simp [pow_two]

private def pairClass {V : Type*} [Fintype V] (C : Finset V) : Finset (Pair V) :=
  Finset.univ.filter (fun e => e.val ∈ C.offDiag.image (Function.uncurry Sym2.mk))

private theorem pairClass_mem {V : Type*} [Fintype V] (C : Finset V) (e : Pair V) :
    e ∈ pairClass C ↔ ∃ u v, u ∈ C ∧ v ∈ C ∧ u ≠ v ∧ e.val = s(u, v) := by
  classical
  constructor
  · intro he
    have he' := (Finset.mem_filter.mp he).2
    rcases Finset.mem_image.mp he' with ⟨⟨u, v⟩, huv, heq⟩
    have huv' := Finset.mem_offDiag.mp huv
    exact ⟨u, v, huv'.1, huv'.2.1, huv'.2.2, by simpa using heq.symm⟩
  · rintro ⟨u, v, hu, hv, huv, hev⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
    exact ⟨(u, v), Finset.mem_offDiag.mpr ⟨hu, hv, huv⟩, by simpa using hev.symm⟩

private theorem pairClass_card {V : Type*} [Fintype V] (C : Finset V) :
    (pairClass C).card = C.card.choose 2 := by
  classical
  let s : Finset (Sym2 V) := C.offDiag.image (Function.uncurry Sym2.mk)
  have hs : ∀ z ∈ s, ¬ z.IsDiag := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨⟨u, v⟩, huv, rfl⟩
    have huv' := (Finset.mem_offDiag.mp huv).2.2
    change ¬ (s(u, v)).IsDiag
    rw [Sym2.mk_isDiag_iff]
    exact huv'
  let e₀ := pairEquivNotDiag V
  let e₁ : {e : Pair V // e.val ∈ s} ≃ {z : Sym2 V // z ∈ s} := {
    toFun := fun e => (⟨e.val.val, e.property⟩ : {z : Sym2 V // z ∈ s})
    invFun := fun z =>
      let z' : {z : Sym2 V // ¬ z.IsDiag} := ⟨z.val, hs z.val z.property⟩
      (⟨e₀.symm z', by change z.val ∈ s; exact z.property⟩ :
        {e : Pair V // e.val ∈ s})
    left_inv := by
      intro e
      apply Subtype.ext
      apply Subtype.ext
      simp [e₀, pairEquivNotDiag]
    right_inv := by
      intro z
      apply Subtype.ext
      simp [e₀, pairEquivNotDiag]
  }
  have e₂ : ↥(pairClass C) ≃ {e : Pair V // e.val ∈ s} := {
    toFun := fun (e : ↥(pairClass C)) =>
      (⟨e.val, (Finset.mem_filter.mp e.property).2⟩ : {e : Pair V // e.val ∈ s})
    invFun := fun (e : {e : Pair V // e.val ∈ s}) =>
      (⟨e.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.property⟩⟩ : ↥(pairClass C))
    left_inv := by intro e; apply Subtype.ext; rfl
    right_inv := by intro e; apply Subtype.ext; rfl
  }
  calc
    (pairClass C).card = Fintype.card ↥(pairClass C) := (Fintype.card_coe _).symm
    _ = Fintype.card {e : Pair V // e.val ∈ s} := Fintype.card_congr e₂
    _ = Fintype.card {z : Sym2 V // z ∈ s} := Fintype.card_congr e₁
    _ = s.card := Fintype.card_coe s
    _ = C.card.choose 2 := Sym2.card_image_offDiag C

private theorem s311_counting_of_deps
    (h09 : ThLean.BP.S3.S3_09aStatement.{u}) :
    ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
      ∀ (G : MGraph V), Colorable q G →
        ((∑ C ∈ frozenClasses q G, C.card) = Fintype.card V ∧
          (∑ C ∈ frozenClasses q G, C.card * (C.card - 1)) =
            2 * (Finset.univ.filter (FrozenPair q G)).card ∧
          (∑ u : V, ((frozenClass q G u).card : ℝ)) =
            (Fintype.card V : ℝ)^2 * classMass q G) := by
  intro V _ q hq hV G hG
  rcases h09 V q hq G hG with ⟨heq, hself, hnon, hdisj, hcover⟩
  let I := frozenClasses q G
  have hU : ∀ u : V, frozenClass q G u ∈ I := by
    intro u
    change frozenClass q G u ∈ frozenClasses q G
    rw [frozenClasses]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, ?_⟩
    exact ⟨u, hself u⟩
  have hclass_eq_of_mem : ∀ (u : V) (C : Finset V), C ∈ I → u ∈ C →
      C = frozenClass q G u := by
    intro u C hC huC
    have hC' : C ∈ frozenClasses q G := by simpa [I] using hC
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hC').1 with ⟨v, -, hCv⟩
    have hvu : Frozen q G v u := by
      have h := huC
      rw [← hCv] at h
      simpa [frozenClass] using h
    have huv := heq.symm hvu
    calc
      C = frozenClass q G v := hCv.symm
      _ = frozenClass q G u := (frozenClass_eq q G heq huv).symm
  have hclass_filter (u : V) : I.filter (fun C => u ∈ C) =
      {frozenClass q G u} := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hC, huC⟩
      exact hclass_eq_of_mem u C hC huC
    · intro hC
      subst C
      exact ⟨hU u, hself u⟩
  have hclass_mem_unique : ∀ u : V, {C ∈ I | u ∈ C}.card = 1 := by
    intro u
    have hcard := congrArg Finset.card (hclass_filter u)
    simpa using hcard
  have hsumClass : (∑ C ∈ I, C.card) = Fintype.card V := by
    rw [Finset.sum_card hclass_mem_unique]
    simp
  let ps := Finset.univ.filter (FrozenPair q G)
  have hpairs_subset : ∀ C ∈ I, pairClass C ⊆ ps := by
    intro C hC e he
    rcases pairClass_mem C e |>.mp he with ⟨u, v, hu, hv, huv, hev⟩
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hC).1 with ⟨w, -, hCw⟩
    have hu' := hu
    have hv' := hv
    rw [← hCw] at hu' hv'
    have hwu : Frozen q G w u := by simpa [frozenClass] using hu'
    have hwv : Frozen q G w v := by simpa [frozenClass] using hv'
    have huw := heq.symm hwu
    have huv' := heq.trans huw hwv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u, v, hev, huv'⟩⟩
  have hpairclass_unique : ∀ e ∈ ps, {C ∈ I | e ∈ pairClass C}.card = 1 := by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with ⟨u, v, hev, huv⟩
    have huvne : u ≠ v := by
      intro h
      subst v
      exact e.property u (by simpa using hev)
    let C := frozenClass q G u
    have hC : C ∈ I := by
      simpa [C] using hU u
    have heC : e ∈ pairClass C := by
      apply (pairClass_mem C e).mpr
      exact ⟨u, v, hself u, by simpa [C, frozenClass] using huv, huvne, hev⟩
    rw [Finset.card_eq_one]
    refine ⟨C, ?_⟩
    ext D
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hD, heD⟩
      rcases pairClass_mem C e |>.mp heC with ⟨a, b, ha, hb, hab, heab⟩
      rcases pairClass_mem D e |>.mp heD with ⟨c, d, hc, hd, hcd, hecd⟩
      have hEq : s(a, b) = s(c, d) := heab.symm.trans hecd
      rcases (Sym2.eq_iff).mp hEq with ⟨hac, hbd⟩ | ⟨had, hbc⟩
      · subst c
        rcases hdisj C hC D hD with hCD | hCD
        · exact hCD.symm
        · exact False.elim (Finset.disjoint_left.mp hCD ha hc)
      · subst d
        rcases hdisj C hC D hD with hCD | hCD
        · exact hCD.symm
        · exact False.elim (Finset.disjoint_left.mp hCD ha hd)
    · intro hD
      subst D
      exact ⟨hC, heC⟩
  have hsumPairClasses : (∑ C ∈ I, (pairClass C).card) = ps.card :=
    sum_card_family_of_unique I ps pairClass hpairs_subset hpairclass_unique
  have hsumOffDiag :
      (∑ C ∈ I, C.card * (C.card - 1)) = 2 * ps.card := by
    have hfactor (C : Finset V) :
        2 * (pairClass C).card = C.card * (C.card - 1) := by
      calc
        2 * (pairClass C).card = 2 * (C.card.choose 2) := by rw [pairClass_card]
        _ = 2 * (C.offDiag.image (Function.uncurry Sym2.mk)).card := by
          rw [← Sym2.card_image_offDiag C]
        _ = C.offDiag.card := Sym2.two_mul_card_image_offDiag C
        _ = C.card * (C.card - 1) := by
          rw [Finset.offDiag_card, Nat.mul_sub_left_distrib]
          simp
    calc
      (∑ C ∈ I, C.card * (C.card - 1)) =
          ∑ C ∈ I, 2 * (pairClass C).card := by
        apply Finset.sum_congr rfl
        intro C hC
        exact (hfactor C).symm
      _ = 2 * (∑ C ∈ I, (pairClass C).card) := by rw [Finset.mul_sum]
      _ = 2 * ps.card := by rw [hsumPairClasses]
  have hsumVertexSizes :
      (∑ u : V, ((frozenClass q G u).card : ℝ)) =
        ∑ C ∈ I, ((C.card : ℝ) ^ 2) := by
    calc
      (∑ u : V, ((frozenClass q G u).card : ℝ)) =
          ∑ u : V, ∑ C ∈ I, if u ∈ C then (C.card : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        calc
          ((frozenClass q G u).card : ℝ) =
              ∑ C ∈ I with u ∈ C, (C.card : ℝ) := by
            rw [hclass_filter u]
            simp
          _ = ∑ C ∈ I, if u ∈ C then (C.card : ℝ) else 0 := by
            rw [Finset.sum_filter]
      _ = ∑ C ∈ I, ∑ u : V, if u ∈ C then (C.card : ℝ) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ C ∈ I, ((C.card : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro C hC
        calc
          (∑ u : V, if u ∈ C then (C.card : ℝ) else 0) =
              ∑ u ∈ C, (C.card : ℝ) := by
            simpa using (Finset.sum_filter (s := (Finset.univ : Finset V))
              (p := fun u : V => u ∈ C) (f := fun _ => (C.card : ℝ))).symm
          _ = (C.card : ℝ) ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul, pow_two]
  have hN : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < Fintype.card V by omega))
  have hmass : (∑ C ∈ I, ((C.card : ℝ) ^ 2)) =
      (Fintype.card V : ℝ) ^ 2 * classMass q G := by
    symm
    rw [classMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C hC
    field_simp [hN]
  refine ⟨hsumClass, ?_, ?_⟩
  · simpa [ps] using hsumOffDiag
  · exact hsumVertexSizes.trans hmass

theorem S3_11Statement_of_deps
    (h03 : ThLean.BP.S3.S3_03aStatement.{u})
    (h09 : ThLean.BP.S3.S3_09aStatement.{u}) :
    ThLean.BP.S3.S3_11Statement.{u} := by
  intro V _ q hq hV
  constructor
  · intro G hG
    exact s311_counting_of_deps h09 V q hq hV G hG
  · intro G
    by_cases hG : Colorable q G
    · let I := frozenClasses q G
      let ps := Finset.univ.filter (FrozenPair q G)
      rcases h09 V q hq G hG with ⟨_, _, hnon, _, _⟩
      have hcount := s311_counting_of_deps h09 V q hq hV G hG
      have hpairCount : (∑ C ∈ I, C.card * (C.card - 1)) = 2 * ps.card := by
        simpa [I, ps] using hcount.2.1
      have hsumSquaresNat : (∑ C ∈ I, C.card ^ 2) =
          2 * ps.card + Fintype.card V := by
        calc
          (∑ C ∈ I, C.card ^ 2) =
              ∑ C ∈ I, (C.card * (C.card - 1) + C.card) := by
            apply Finset.sum_congr rfl
            intro C hC
            have hcard : 1 ≤ C.card :=
              Nat.succ_le_iff.mpr (Finset.card_pos.mpr (hnon C (by simpa [I] using hC)))
            exact (nat_mul_pred_add_self C.card hcard).symm
          _ = (∑ C ∈ I, C.card * (C.card - 1)) + (∑ C ∈ I, C.card) :=
            Finset.sum_add_distrib
          _ = 2 * ps.card + Fintype.card V := by
            rw [hpairCount, hcount.1]
      have hsumSquaresReal :
          (∑ C ∈ I, ((C.card : ℝ) ^ 2)) =
            2 * (ps.card : ℝ) + (Fintype.card V : ℝ) := by
        exact_mod_cast hsumSquaresNat
      have hN : (Fintype.card V : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (show 0 < Fintype.card V by omega))
      have hNgt : (1 : ℝ) < (Fintype.card V : ℝ) := by
        exact_mod_cast (show 1 < Fintype.card V by omega)
      have hNm1 : (Fintype.card V : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
      have hdiv : 2 ∣ Fintype.card V * (Fintype.card V - 1) := by
        rcases Nat.even_or_odd (Fintype.card V) with hEven | hOdd
        · exact even_iff_two_dvd.mp (Even.mul_right hEven (Fintype.card V - 1))
        · have hPredEven : Even (Fintype.card V - 1) := by
            rcases hOdd with ⟨k, hk⟩
            refine ⟨k, ?_⟩
            omega
          exact even_iff_two_dvd.mp (Even.mul_left hPredEven (Fintype.card V))
      have hchooseDouble :
          2 * (Fintype.card V).choose 2 = Fintype.card V * (Fintype.card V - 1) := by
        rw [Nat.choose_two_right]
        exact Nat.mul_div_cancel' hdiv
      have hPairCard : Fintype.card (Pair V) = (Fintype.card V).choose 2 :=
        (h03 V hV).1
      have hPairDouble :
          2 * Fintype.card (Pair V) = Fintype.card V * (Fintype.card V - 1) := by
        rw [hPairCard]
        exact hchooseDouble
      have hPairDoubleReal :
          (2 : ℝ) * (Fintype.card (Pair V) : ℝ) =
            (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
        have hcast : ((2 * Fintype.card (Pair V) : ℕ) : ℝ) =
            ((Fintype.card V * (Fintype.card V - 1) : ℕ) : ℝ) := by
          exact_mod_cast hPairDouble
        calc
          (2 : ℝ) * (Fintype.card (Pair V) : ℝ) =
              ((2 * Fintype.card (Pair V) : ℕ) : ℝ) := by norm_num
          _ = ((Fintype.card V * (Fintype.card V - 1) : ℕ) : ℝ) := hcast
          _ = (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
            rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ Fintype.card V by omega)]
            norm_num
      have hPairReal : (Fintype.card (Pair V) : ℝ) =
          (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2 := by
        linarith [hPairDoubleReal]
      have hkappa : kappa q G = (ps.card : ℝ) / (Fintype.card (Pair V) : ℝ) := by
        simp [kappa, uniformProb, uniformMean, ps, indicator]
      have hscale : (Fintype.card V : ℝ) ^ 2 * classMass q G =
          ∑ C ∈ I, ((C.card : ℝ) ^ 2) := by
        rw [classMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C hC
        field_simp [hN]
      have hmass : classMass q G =
          (2 * (ps.card : ℝ) + (Fintype.card V : ℝ)) /
            (Fintype.card V : ℝ) ^ 2 := by
        calc
          classMass q G =
              ((Fintype.card V : ℝ) ^ 2 * classMass q G) /
                (Fintype.card V : ℝ) ^ 2 := by field_simp [hN]
          _ = (∑ C ∈ I, ((C.card : ℝ) ^ 2)) /
                (Fintype.card V : ℝ) ^ 2 := by rw [hscale]
          _ = _ := by rw [hsumSquaresReal]
      have hformula : classMass q G =
          (1 - 1 / (Fintype.card V : ℝ)) * kappa q G +
            1 / (Fintype.card V : ℝ) := by
        calc
          classMass q G =
              (2 * (ps.card : ℝ) + (Fintype.card V : ℝ)) /
                (Fintype.card V : ℝ) ^ 2 := hmass
          _ = (1 - 1 / (Fintype.card V : ℝ)) * kappa q G +
                1 / (Fintype.card V : ℝ) := by
            rw [hkappa, hPairReal]
            field_simp [hN, hNm1]
      simpa [indicator, hG] using hformula
    · have hclass (u : V) : frozenClass q G u = ∅ := by
        ext v
        simp [frozenClass, Frozen, hG]
      have hclasses : frozenClasses q G = ∅ := by
        simp [frozenClasses, hclass]
      simp [classMass, hclasses, kappa, uniformProb, uniformMean,
        FrozenPair, Frozen, indicator, hG]

end ThLean.W.S307

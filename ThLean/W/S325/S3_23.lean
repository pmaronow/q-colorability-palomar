import ThLean.BP.S3.Lifetime

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ThLean.W.S325
open ThLean.BP.S3 ThresholdFoundations

universe u

private lemma sum_colorClassSize {V : Type u} [Fintype V] {q : ℕ}
    (σ : V → Fin q) :
    (∑ i : Fin q, (colorClassSize σ i : ℝ)) = Fintype.card V := by
  classical
  have hcard (i : Fin q) : colorClassSize σ i = Fintype.card {v : V // σ v = i} := by
    simp [colorClassSize, Fintype.card_subtype]
  have hnat : ∑ i : Fin q, colorClassSize σ i = Fintype.card V := by
    calc
      _ = ∑ i : Fin q, Fintype.card {v : V // σ v = i} :=
        Finset.sum_congr rfl (fun i _ => hcard i)
      _ = Fintype.card (Σ i : Fin q, {v : V // σ v = i}) := by
        rw [Fintype.card_sigma]
      _ = Fintype.card V := Fintype.card_congr (Equiv.sigmaFiberEquiv σ)
  exact_mod_cast hnat

private lemma class_square_lower {V : Type u} [Fintype V] (q : ℕ) (hq : 0 < q)
    (σ : V → Fin q) :
    (Fintype.card V : ℝ)^2 / q ≤ ∑ i : Fin q, (colorClassSize σ i : ℝ)^2 := by
  classical
  let n : Fin q → ℝ := fun i => (colorClassSize σ i : ℝ)
  have hn : ∑ i, n i = Fintype.card V := by
    simpa [n] using sum_colorClassSize σ
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hs : 0 ≤ ∑ i : Fin q, (n i - (Fintype.card V : ℝ) / q)^2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hlin : ∑ i : Fin q, (2 * n i * ((Fintype.card V : ℝ) / q)) =
      2 * ((Fintype.card V : ℝ) / q) * Fintype.card V := by
    calc
      _ = (∑ i : Fin q, n i) * (2 * ((Fintype.card V : ℝ) / q)) := by
        calc
          _ = ∑ i : Fin q, n i * (2 * ((Fintype.card V : ℝ) / q)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [hn]; ring
  have hconst : ∑ _i : Fin q, ((Fintype.card V : ℝ) / q)^2 =
      q * ((Fintype.card V : ℝ) / q)^2 := by simp
  have hexpand :
      ∑ i : Fin q, (n i - (Fintype.card V : ℝ) / q)^2 =
      (∑ i : Fin q, (n i)^2) - 2 * ((Fintype.card V : ℝ) / q) * Fintype.card V +
        q * ((Fintype.card V : ℝ) / q)^2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hlin, hconst]
  rw [hexpand] at hs
  have hcancel :
      2 * ((Fintype.card V : ℝ) / q) * Fintype.card V -
          q * ((Fintype.card V : ℝ) / q)^2 =
        (Fintype.card V : ℝ)^2 / q := by
    field_simp
    ring
  have hmain : (Fintype.card V : ℝ)^2 / q ≤ ∑ i : Fin q, n i ^ 2 := by
    nlinarith [hs, hcancel]
  simpa [n] using hmain

private lemma sym2_isDiag_iff_exists {V : Type u} (e : Sym2 V) :
    e.IsDiag ↔ ∃ v, e = s(v,v) := by
  induction e using Sym2.ind with
  | h a b =>
      simp only [Sym2.mk_isDiag_iff]
      constructor
      · intro hab
        exact ⟨a, by subst b; rfl⟩
      · rintro ⟨v, hv⟩
        have h := (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (v,v))).mp hv
        rcases h with h | h
        · have ha : a = v := by simpa using congrArg Prod.fst h
          have hb : b = v := by simpa using congrArg Prod.snd h
          exact ha.trans hb.symm
        · have ha : a = v := by simpa using congrArg Prod.fst h
          have hb : b = v := by simpa using congrArg Prod.snd h
          exact ha.trans hb.symm

private lemma pair_property_iff_not_diag {V : Type u} (e : Sym2 V) :
    (∀ v : V, e ≠ s(v,v)) ↔ ¬ e.IsDiag := by
  rw [sym2_isDiag_iff_exists]
  simp

private def pairEquivNotDiag {V : Type u} :
    Pair V ≃ {e : Sym2 V // ¬ e.IsDiag} where
  toFun e := ⟨e.val, (pair_property_iff_not_diag e.val).mp e.property⟩
  invFun e := ⟨e.val, (pair_property_iff_not_diag e.val).mpr e.property⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

private lemma pair_card {V : Type u} [Fintype V] :
    Fintype.card (Pair V) = (Fintype.card V).choose 2 := by
  classical
  exact (Fintype.card_congr pairEquivNotDiag).trans Sym2.card_subtype_not_diag

private noncomputable def classPairsSym {V : Type u} [Fintype V] [DecidableEq V] {q : ℕ}
    (σ : V → Fin q) (i : Fin q) : Finset (Sym2 V) := by
  classical
  exact (Finset.univ.filter (fun v : V => σ v = i)).sym2.filter (fun e => ¬e.IsDiag)

private lemma classPairsSym_eq_image {V : Type u} [Fintype V] [DecidableEq V] {q : ℕ}
    (σ : V → Fin q) (i : Fin q) :
    classPairsSym σ i =
      ((Finset.univ.filter (fun v : V => σ v = i)).offDiag.image Sym2.mk.uncurry) := by
  rw [classPairsSym, Finset.sym2_eq_image]
  simpa using (Sym2.filter_image_mk_not_isDiag
    (Finset.univ.filter (fun v : V => σ v = i)))

private lemma classPairsSym_mem {V : Type u} [Fintype V] [DecidableEq V] {q : ℕ}
    (σ : V → Fin q) (i : Fin q) (e : Sym2 V) :
    e ∈ classPairsSym σ i ↔ ¬e.IsDiag ∧ ∀ v ∈ e, σ v = i := by
  classical
  simp [classPairsSym, Finset.mem_sym2_iff, and_comm]

private lemma classPairsSym_card {V : Type u} [Fintype V] [DecidableEq V] {q : ℕ}
    (σ : V → Fin q) (i : Fin q) :
    (classPairsSym σ i).card = (colorClassSize σ i).choose 2 := by
  classical
  rw [classPairsSym_eq_image, Sym2.card_image_offDiag]
  rfl

private noncomputable def monoPairsSym {V : Type u} [Fintype V] {q : ℕ}
    (σ : V → Fin q) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter (fun e => ¬e.IsDiag ∧ ∃ u v, e = s(u,v) ∧ σ u = σ v)

private def monoNotDiagEquiv {V : Type u} [Fintype V] {q : ℕ}
    (σ : V → Fin q) :
    {e : {e : Sym2 V // ¬e.IsDiag} // ∃ u v, e.val = s(u,v) ∧ σ u = σ v} ≃
      {e : Sym2 V // e ∈ monoPairsSym σ} where
  toFun e := ⟨e.val.val, by
    simp only [monoPairsSym, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e.val.property, e.property⟩⟩
  invFun e := by
    have he := e.property
    simp only [monoPairsSym, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact ⟨⟨e.val, he.1⟩, he.2⟩
  left_inv e := by cases e with | mk a ha => cases a with | mk b hb => rfl
  right_inv e := by cases e; rfl

private lemma sum_indicator_eq_subtype_card {α : Type u} [Fintype α]
    (P : α → Prop) [Fintype {x // P x}] :
    (∑ x : α, indicator (P x)) = (Fintype.card {x // P x} : ℝ) := by
  classical
  simp [indicator, Fintype.card_subtype]

private lemma mono_pair_iff_const {V : Type u} {q : ℕ} (σ : V → Fin q) (e : Sym2 V) :
    (∃ u v, e = s(u,v) ∧ σ u = σ v) ↔ ∃ i, ∀ v ∈ e, σ v = i := by
  constructor
  · rintro ⟨u,v,rfl,h⟩
    exact ⟨σ u, Sym2.ball.mpr ⟨rfl,h.symm⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨p, hp⟩ := Sym2.mk_surjective e
    rcases p with ⟨u,v⟩
    have he : e = s(u,v) := hp.symm
    refine ⟨u,v,he, ?_⟩
    have hu : σ u = i := hi u (by rw [he]; exact Sym2.mem_mk_left u v)
    have hv : σ v = i := hi v (by rw [he]; exact Sym2.mem_mk_right u v)
    exact hu.trans hv.symm

private lemma monoPairsSym_biUnion {V : Type u} [Fintype V] [DecidableEq V] {q : ℕ}
    (σ : V → Fin q) :
    Finset.univ.biUnion (classPairsSym σ) = monoPairsSym σ := by
  classical
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, monoPairsSym,
    Finset.mem_filter, Finset.mem_univ, true_and, classPairsSym_mem]
  constructor
  · rintro ⟨i, hnd, hconst⟩
    exact ⟨hnd, (mono_pair_iff_const σ e).mpr ⟨i,hconst⟩⟩
  · rintro ⟨hnd, hmono⟩
    obtain ⟨i,hconst⟩ := (mono_pair_iff_const σ e).mp hmono
    exact ⟨i,hnd,hconst⟩

private lemma classPairsSym_pairwiseDisjoint {V : Type u} [Fintype V] [DecidableEq V]
    {q : ℕ} (σ : V → Fin q) :
    ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint
      (classPairsSym σ) := by
  classical
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hci := (classPairsSym_mem σ i e).mp hei
  have hcj := (classPairsSym_mem σ j e).mp hej
  have hu := hci.2 e.out.1 (Sym2.out_fst_mem e)
  have hv := hcj.2 e.out.1 (Sym2.out_fst_mem e)
  exact hij (hu.symm.trans hv)

private lemma monoPairsSym_card {V : Type u} [Fintype V] {q : ℕ}
    (σ : V → Fin q) :
    (monoPairsSym σ).card = ∑ i : Fin q, (colorClassSize σ i).choose 2 := by
  classical
  rw [← monoPairsSym_biUnion]
  rw [Finset.card_biUnion (classPairsSym_pairwiseDisjoint σ)]
  simp_rw [classPairsSym_card]

private lemma monoPairProb_eq_card_ratio {V : Type u} [Fintype V] {q : ℕ}
    (σ : V → Fin q) :
    monoPairProb σ = (monoPairsSym σ).card / Fintype.card (Pair V) := by
  classical
  have hsum :
      (∑ p : Pair V, indicator (∃ u v, p.val = s(u,v) ∧ σ u = σ v)) =
        (monoPairsSym σ).card := by
    calc
      _ = ∑ e : {e : Sym2 V // ¬e.IsDiag},
          indicator (∃ u v, e.val = s(u,v) ∧ σ u = σ v) :=
        Fintype.sum_equiv pairEquivNotDiag _ _ (by intro p; rfl)
      _ = (monoPairsSym σ).card := by
        calc
          (∑ e : {e : Sym2 V // ¬e.IsDiag},
              indicator (∃ u v, e.val = s(u,v) ∧ σ u = σ v)) =
              Fintype.card
                {e : {e : Sym2 V // ¬e.IsDiag} //
                  ∃ u v, e.val = s(u,v) ∧ σ u = σ v} := by
                exact_mod_cast (sum_indicator_eq_subtype_card
                  (α := {e : Sym2 V // ¬e.IsDiag})
                  (fun e => ∃ u v, e.val = s(u,v) ∧ σ u = σ v))
          _ = Fintype.card {e : Sym2 V // e ∈ monoPairsSym σ} :=
                by exact_mod_cast Fintype.card_congr (monoNotDiagEquiv σ)
          _ = (monoPairsSym σ).card := by exact_mod_cast Fintype.card_coe _
  unfold monoPairProb uniformProb uniformMean
  change (∑ p : Pair V, indicator (∃ u v, p.val = s(u,v) ∧ σ u = σ v)) /
      (Fintype.card (Pair V) : ℝ) = (monoPairsSym σ).card /
      (Fintype.card (Pair V) : ℝ)
  rw [hsum]

private lemma monoPairProb_classFormula {V : Type u} [Fintype V] {q : ℕ}
    (σ : V → Fin q) :
    monoPairProb σ =
      (∑ i : Fin q, ((colorClassSize σ i).choose 2 : ℝ)) /
        (Fintype.card (Pair V) : ℝ) := by
  rw [monoPairProb_eq_card_ratio, monoPairsSym_card]
  simp only [Nat.cast_sum]

theorem S3_23Statement_holds : ThLean.BP.S3.S3_23Statement := by
  classical
  intro V inst q hq hV σ
  have hqN : 0 < q := by omega
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hqN
  let N : ℝ := Fintype.card V
  let n : Fin q → ℝ := fun i => (colorClassSize σ i : ℝ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Nat.zero_lt_of_lt hV)
  have hN1 : 1 < N := by
    dsimp [N]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hV)
  have hsum : ∑ i : Fin q, n i = N := by
    simpa [N, n] using sum_colorClassSize σ
  have hsq : N^2 / (q : ℝ) ≤ ∑ i : Fin q, n i^2 := by
    simpa [N, n] using class_square_lower q hqN σ
  have hpair := pair_card (V := V)
  have hpairR : (Fintype.card (Pair V) : ℝ) = N * (N - 1) / 2 := by
    rw [hpair]
    simp [N, Nat.cast_choose_two]
  have hnum :
      (∑ i : Fin q, ((colorClassSize σ i).choose 2 : ℝ)) =
        (∑ i : Fin q, n i * (n i - 1)) / 2 := by
    calc
      _ = ∑ i : Fin q, (n i * (n i - 1) / 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [n, Nat.cast_choose_two]
      _ = _ := by rw [← Finset.sum_div]
  have hprob : monoPairProb σ =
      (∑ i : Fin q, n i * (n i - 1)) / (N * (N - 1)) := by
    calc
      monoPairProb σ =
          (∑ i : Fin q, ((colorClassSize σ i).choose 2 : ℝ)) /
            (Fintype.card (Pair V) : ℝ) := monoPairProb_classFormula σ
      _ = ((∑ i : Fin q, n i * (n i - 1)) / 2) / (N * (N - 1) / 2) := by
        rw [hnum, hpairR]
      _ = _ := by
        field_simp [ne_of_gt hNpos, ne_of_gt hN1]
  have hprod :
      (∑ i : Fin q, n i * (n i - 1)) = (∑ i : Fin q, n i^2) - N := by
    calc
      _ = ∑ i : Fin q, (n i^2 - n i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i : Fin q, n i^2) - (∑ i : Fin q, n i) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by rw [hsum]
  have hcross : N^2 / (q : ℝ) - N ≤ ∑ i : Fin q, n i * (n i - 1) := by
    rw [hprod]
    linarith [hsq]
  have hden : 0 < N * (N - 1) := mul_pos hNpos (sub_pos.mpr hN1)
  have hratio :
      (N^2 / (q : ℝ) - N) / (N * (N - 1)) ≤
        (∑ i : Fin q, n i * (n i - 1)) / (N * (N - 1)) :=
    (div_le_div_iff_of_pos_right hden).2 hcross
  have hbaseEq :
      (N / (q : ℝ) - 1) / (N - 1) =
        (N^2 / (q : ℝ) - N) / (N * (N - 1)) := by
    field_simp [ne_of_gt hqR, ne_of_gt hNpos, ne_of_gt hN1]
  have hlower : (N / (q : ℝ) - 1) / (N - 1) ≤ monoPairProb σ := by
    rw [hbaseEq, hprob]
    exact hratio
  have hthird :
      2*q ≤ Fintype.card V → 1 / (2 * (q : ℝ)) ≤ monoPairProb σ := by
    intro hlarge
    have hNlarge : 2 * (q : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast hlarge
    have hqcancel : (N / (q : ℝ)) * q = N := by
      field_simp [ne_of_gt hqR]
    have hbaseLower :
        1 / (2 * (q : ℝ)) ≤ (N / (q : ℝ) - 1) / (N - 1) := by
      apply (div_le_div_iff₀ (by positivity) (sub_pos.mpr hN1)).2
      nlinarith [hNlarge, hqcancel]
    exact hbaseLower.trans hlower
  have hupperEq :
      1 - (N / (q : ℝ) - 1) / (N - 1) =
        (((q : ℝ) - 1) / q) * (N / (N - 1)) := by
    field_simp [ne_of_gt hqR, ne_of_gt (sub_pos.mpr hN1)]
    ; ring
  have hupper :
      1 - monoPairProb σ ≤ (((q : ℝ) - 1) / q) *
        ((Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 1)) := by
    calc
      _ ≤ 1 - (N / (q : ℝ) - 1) / (N - 1) := sub_le_sub_left hlower 1
      _ = (((q : ℝ) - 1) / q) * (N / (N - 1)) := hupperEq
      _ = _ := by simp [N]
  exact ⟨class_square_lower q hqN σ, hlower, hthird, hupper⟩

end ThLean.W.S325

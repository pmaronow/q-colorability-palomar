import ThLean.BP.S6.Descent

noncomputable section
open scoped BigOperators
open ThresholdFoundations

namespace ThLean.W.S636

open ThLean.BP.S6

private lemma frozen_symm {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V)
    {a b : V} (h : Frozen q G a b) : Frozen q G b a := by
  exact ⟨h.1, fun σ hc => (h.2 σ hc).symm⟩

private def pairOf {n : ℕ} (a b : Fin n) (hab : a ≠ b) : Edge n :=
  ⟨s(a, b), by
    intro v hv
    rcases Sym2.eq_iff.mp hv with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hab (ha.trans hb.symm)
    · exact hab (ha.trans hb.symm)⟩

private lemma frozenPair_pairOf_iff {n q : ℕ} (G : Graph n) (a b : Fin n)
    (hab : a ≠ b) : FrozenPair q G (pairOf a b hab) ↔ Frozen q G a b := by
  constructor
  · rintro ⟨u, v, huv, hf⟩
    have heq : s(a, b) = s(u, v) := by
      simpa [pairOf] using huv
    rcases Sym2.eq_iff.mp heq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
    · subst u
      subst v
      exact hf
    · subst v
      subst u
      exact frozen_symm q G hf
  · intro hf
    exact ⟨a, b, by simp [pairOf], hf⟩

private lemma highEdge_pairOf_iff {n : ℕ} (G : Graph n) (D : ℕ)
    (a b : Fin n) (hab : a ≠ b) :
    highEdge G D (pairOf a b hab) ↔ D < degree G a ∨ D < degree G b := by
  constructor
  · rintro ⟨u, ⟨v, huv⟩, hd⟩
    have heq : s(a, b) = s(u, v) := by simpa [pairOf] using huv
    rcases Sym2.eq_iff.mp heq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
    · left
      simpa [hau] using hd
    · right
      simpa [hbu] using hd
  · rintro (ha | hb)
    · exact ⟨a, ⟨b, by simp [pairOf]⟩, ha⟩
    · exact ⟨b, ⟨a, Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩, hb⟩

private lemma pair_event_iff {n q : ℕ} (G : Graph n) (D : ℕ) (a b : Fin n) :
    (∃ e : Edge n, e.val = s(a, b) ∧ FrozenPair q G e ∧ highEdge G D e) ↔
      a ≠ b ∧ Frozen q G a b ∧ (D < degree G a ∨ D < degree G b) := by
  constructor
  · rintro ⟨e, he, hfr, hhi⟩
    have hab : a ≠ b := by
      intro hab
      subst b
      exact e.property a (by simpa using he)
    have ep : e = pairOf a b hab := Subtype.ext (by simpa [pairOf] using he)
    subst e
    exact ⟨hab, (frozenPair_pairOf_iff G a b hab).mp hfr,
      (highEdge_pairOf_iff G D a b hab).mp hhi⟩
  · rintro ⟨hab, hfr, hhi⟩
    exact ⟨pairOf a b hab, by simp [pairOf],
      (frozenPair_pairOf_iff G a b hab).mpr hfr,
      (highEdge_pairOf_iff G D a b hab).mpr hhi⟩

private lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split <;> norm_num

private lemma kappaDegree_pos_of_frozen {n q j : ℕ} (G : Graph n)
    (a b : Fin n) (hab : a ≠ b) (hfr : Frozen q G a b)
    (hd : degree G a = j) : 0 < kappaDegree q j G := by
  unfold kappaDegree
  have ht : indicator (a ≠ b ∧ Frozen q G a b ∧ degree G a = j) = 1 := by
    simp [indicator, hab, hfr, hd]
  have hin : 1 ≤ ∑ v : Fin n,
      indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j) := by
    calc
      1 = indicator (a ≠ b ∧ Frozen q G a b ∧ degree G a = j) := ht.symm
      _ ≤ ∑ v : Fin n,
          indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j) :=
        Finset.single_le_sum
          (f := fun v : Fin n => indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j))
          (fun v _ => indicator_nonneg _) (Finset.mem_univ b)
  have hout : (∑ v : Fin n,
      indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j)) ≤
      ∑ u : Fin n, ∑ v : Fin n,
        indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j) :=
    Finset.single_le_sum (f := fun u : Fin n =>
      ∑ v : Fin n, indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j))
      (fun u _ => Finset.sum_nonneg fun v _ => indicator_nonneg _)
      (Finset.mem_univ a)
  have hnum : 0 < ∑ u : Fin n, ∑ v : Fin n,
      indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j) := by linarith
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
    have hn' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    positivity
  have hnnum : 0 <
      (∑ u : Fin n, ∑ v : Fin n,
        indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j)) /
        ((Fintype.card (Fin n) : ℝ) * ((Fintype.card (Fin n) : ℝ) - 1)) := by
    simpa [Fintype.card_fin] using div_pos hnum hden
  exact hnnum

private lemma tupleGraph_edgeCount {n m : ℕ} (x : Hist n m) :
    edgeCount (tupleGraph x) = m := by
  classical
  simpa [edgeCount, tupleGraph] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin m)) (Finset.univ : Finset (Sym2 (Fin n)))
      (fun i : Fin m => (x i).val))

private lemma degree_le_edgeCount {n q : ℕ} (h04 : S6_04aStatement)
    (hn : 3 ≤ n) (hq : 3 ≤ q) (G : Graph n) (a b : Fin n)
    (hab : a ≠ b) (hfr : Frozen q G a b) : degree G a ≤ edgeCount G := by
  by_contra hnot
  have hgt : edgeCount G < degree G a := by omega
  have hsupp := ((h04 n q hn hq G (degree G a) 1
    (by omega)).2.2.2.2.2.2) hgt
  have hpos := kappaDegree_pos_of_frozen G a b hab hfr rfl
  rw [hsupp.1] at hpos
  exact (lt_irrefl _ hpos)

private lemma sum_triple_reorder {n : ℕ} (J : Finset ℕ)
    (f : ℕ → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ j ∈ J, f j a b) =
      ∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, f j a b := by
  classical
  calc
    (∑ a : Fin n, ∑ b : Fin n, ∑ j ∈ J, f j a b) =
        ∑ a : Fin n, ∑ j ∈ J, ∑ b : Fin n, f j a b := by
      apply Finset.sum_congr rfl
      intro a ha
      simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))
        (t := J) (f := fun b j => f j a b))
    _ = ∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, f j a b := by
      simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))
        (t := J) (f := fun a j => ∑ b : Fin n, f j a b))

private lemma sum_triple_swap {n : ℕ} (J : Finset ℕ)
    (f : ℕ → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ j ∈ J, f j b a) =
      ∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, f j a b := by
  classical
  calc
    (∑ a : Fin n, ∑ b : Fin n, ∑ j ∈ J, f j b a) =
        ∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, f j b a :=
      sum_triple_reorder J (fun j a b => f j b a)
    _ = ∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, f j a b := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ a : Fin n, ∑ b : Fin n, f j b a) =
            ∑ b : Fin n, ∑ a : Fin n, f j b a := Finset.sum_comm
        _ = ∑ a : Fin n, ∑ b : Fin n, f j a b := rfl

private lemma graph_high_count {n q m D : ℕ} (h03 : S6_03Statement)
    (h04 : S6_04aStatement) (hn : 3 ≤ n) (hq : 3 ≤ q)
    (G : Graph n) (hcount : edgeCount G = m) :
    kappaKind q (fun G e => highEdge G D e) G ≤
      2 * ∑ j ∈ Finset.Ico (D + 1) (m + 1), kappaDegree q j G := by
  classical
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  let instFrozen : Fintype (Edge n) :=
    @Subtype.fintype (Sym2 (Fin n)) (fun e => ∀ v : Fin n, e ≠ s(v, v))
      (fun e => Fintype.decidableForallFintype) Sym2.instFintype
  letI : Fintype (Edge n) := instFrozen
  let J : Finset ℕ := Finset.Ico (D + 1) (m + 1)
  let C : ℕ → Fin n → Fin n → ℝ := fun j a b =>
    indicator (a ≠ b ∧ Frozen q G a b ∧ degree G a = j)
  let H : Sym2 (Fin n) → ℝ := fun e =>
    indicator (∃ p : Edge n, p.val = e ∧ FrozenPair q G p ∧ highEdge G D p)
  have hevent (a b : Fin n) :
      (∃ p : Edge n, p.val = s(a, b) ∧ FrozenPair q G p ∧ highEdge G D p) ↔
        a ≠ b ∧ Frozen q G a b ∧ (D < degree G a ∨ D < degree G b) :=
    pair_event_iff G D a b
  have hEdge (e : Edge n) :
      (∃ p : Edge n, p.val = e.val ∧ FrozenPair q G p ∧ highEdge G D p) ↔
        FrozenPair q G e ∧ highEdge G D e := by
    constructor
    · rintro ⟨p, hp, hf, hh⟩
      have hpe : p = e := Subtype.ext hp
      subst p
      exact ⟨hf, hh⟩
    · rintro ⟨hf, hh⟩
      exact ⟨e, rfl, hf, hh⟩
  have hmean :
      uniformProb (fun e : Edge n => FrozenPair q G e ∧ highEdge G D e) =
        uniformMean (fun e : Edge n => H e.val) := by
    unfold uniformProb uniformMean
    apply congrArg (fun z : ℝ => z / (Fintype.card (Edge n) : ℝ))
    apply Finset.sum_congr rfl
    intro e he
    change indicator (FrozenPair q G e ∧ highEdge G D e) =
      indicator (∃ p : Edge n, p.val = e.val ∧ FrozenPair q G p ∧ highEdge G D p)
    exact congrArg indicator (propext (hEdge e).symm)
  have hrepr := (h03 n hn).2.1 H
  have hrepr' :
      @uniformMean (Edge n) instFrozen (fun e : Edge n => H e.val) =
        (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) * H (s(a, b))) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
    let inst03 : Fintype (Edge n) := by
      letI : DecidableEq (Fin n) := instDecidableEqFin n
      let dec03 : DecidablePred
          (fun e : Sym2 (Fin n) => ∀ v : Fin n, e ≠ s(v, v)) := fun e =>
        @Nat.decidableForallFin n (fun v : Fin n => e ≠ s(v, v)) (fun v => inferInstance)
      exact @Subtype.fintype (Sym2 (Fin n))
        (fun e => ∀ v : Fin n, e ≠ s(v, v)) dec03 Sym2.instFintype
    have hinst : inst03 = instFrozen := Subsingleton.elim _ _
    rw [← hinst]
    simpa [Fintype.card_fin] using hrepr
  have hkind :
      kappaKind q (fun G e => highEdge G D e) G =
        (∑ a : Fin n, ∑ b : Fin n,
          indicator (a ≠ b) *
            indicator (a ≠ b ∧ Frozen q G a b ∧
              (D < degree G a ∨ D < degree G b))) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
    calc
      kappaKind q (fun G e => highEdge G D e) G =
          uniformProb (fun e : Edge n => FrozenPair q G e ∧ highEdge G D e) := rfl
      _ = uniformMean (fun e : Edge n => H e.val) := hmean
      _ = (∑ a : Fin n, ∑ b : Fin n,
            indicator (a ≠ b) * H (s(a, b))) /
            ((n : ℝ) * ((n : ℝ) - 1)) := hrepr'
      _ = (∑ a : Fin n, ∑ b : Fin n,
            indicator (a ≠ b) *
              indicator (a ≠ b ∧ Frozen q G a b ∧
                (D < degree G a ∨ D < degree G b))) /
            ((n : ℝ) * ((n : ℝ) - 1)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        simp only [H, hevent]
  have hpoint (a b : Fin n) :
      indicator (a ≠ b) *
          indicator (a ≠ b ∧ Frozen q G a b ∧
            (D < degree G a ∨ D < degree G b)) ≤
        ∑ j ∈ J, (C j a b + C j b a) := by
    by_cases he : a ≠ b ∧ Frozen q G a b ∧
        (D < degree G a ∨ D < degree G b)
    · rcases he with ⟨hab, hfr, hhi⟩
      rcases hhi with ha | hb
      · have hdeg := degree_le_edgeCount h04 hn hq G a b hab hfr
        have hdegM : degree G a ≤ m := by rw [← hcount]; exact hdeg
        let j := degree G a
        have hjmem : j ∈ J := by
          simp [J, j, Finset.mem_Ico]
          omega
        have hterm : C j a b = 1 := by
          simp [C, j, indicator, hab, hfr]
        have hnon : 0 ≤ C j b a := by
          exact indicator_nonneg _
        have hsingle : C j a b + C j b a ≤ ∑ j ∈ J, (C j a b + C j b a) :=
          Finset.single_le_sum
            (f := fun j : ℕ => C j a b + C j b a)
            (fun j _ => add_nonneg (indicator_nonneg _) (indicator_nonneg _)) hjmem
        have hge : 1 ≤ C j a b + C j b a := by rw [hterm]; linarith
        calc
          _ = 1 := by simp [indicator, hab, hfr, ha]
          _ ≤ C j a b + C j b a := hge
          _ ≤ _ := hsingle
      · have hfr' : Frozen q G b a := frozen_symm q G hfr
        have hdeg := degree_le_edgeCount h04 hn hq G b a hab.symm hfr'
        have hdegM : degree G b ≤ m := by rw [← hcount]; exact hdeg
        let j := degree G b
        have hjmem : j ∈ J := by
          simp [J, j, Finset.mem_Ico]
          omega
        have hterm : C j b a = 1 := by
          simp [C, j, indicator, hab.symm, hfr']
        have hnon : 0 ≤ C j a b := indicator_nonneg _
        have hsingle : C j a b + C j b a ≤ ∑ j ∈ J, (C j a b + C j b a) :=
          Finset.single_le_sum
            (f := fun j : ℕ => C j a b + C j b a)
            (fun j _ => add_nonneg (indicator_nonneg _) (indicator_nonneg _)) hjmem
        have hge : 1 ≤ C j a b + C j b a := by rw [hterm]; linarith
        calc
          _ = 1 := by simp [indicator, hab, hfr, hb]
          _ ≤ C j a b + C j b a := hge
          _ ≤ _ := hsingle
    · have hnon : 0 ≤ ∑ j ∈ J, (C j a b + C j b a) :=
        Finset.sum_nonneg fun j _ => add_nonneg (indicator_nonneg _) (indicator_nonneg _)
      calc
        _ = 0 := by simp [indicator, he]
        _ ≤ _ := hnon
  have hnum :
      (∑ a : Fin n, ∑ b : Fin n,
        indicator (a ≠ b) *
          indicator (a ≠ b ∧ Frozen q G a b ∧
            (D < degree G a ∨ D < degree G b))) ≤
        2 * ∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, C j a b := by
    calc
      _ ≤ ∑ a : Fin n, ∑ b : Fin n, ∑ j ∈ J, (C j a b + C j b a) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact hpoint a b
      _ = 2 * ∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, C j a b := by
        simp_rw [Finset.sum_add_distrib]
        rw [sum_triple_reorder J C, sum_triple_swap J C]
        ring
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
    have hn' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    positivity
  calc
    kappaKind q (fun G e => highEdge G D e) G =
        (∑ a : Fin n, ∑ b : Fin n,
          indicator (a ≠ b) *
            indicator (a ≠ b ∧ Frozen q G a b ∧
              (D < degree G a ∨ D < degree G b))) /
          ((n : ℝ) * ((n : ℝ) - 1)) := hkind
    _ ≤ (2 * ∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, C j a b) /
          ((n : ℝ) * ((n : ℝ) - 1)) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ = 2 * ∑ j ∈ J, kappaDegree q j G := by
      unfold kappaDegree
      simp only [Fintype.card_fin]
      change (2 * ∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, C j a b) /
          ((n : ℝ) * ((n : ℝ) - 1)) =
        2 * ∑ j ∈ J,
          (∑ a : Fin n, ∑ b : Fin n, C j a b) /
            ((n : ℝ) * ((n : ℝ) - 1))
      calc
        _ = 2 * ((∑ j ∈ J, ∑ a : Fin n, ∑ b : Fin n, C j a b) /
              ((n : ℝ) * ((n : ℝ) - 1))) := by ring
        _ = 2 * ∑ j ∈ J,
              (∑ a : Fin n, ∑ b : Fin n, C j a b) /
                ((n : ℝ) * ((n : ℝ) - 1)) := by rw [Finset.sum_div]

private lemma uniformMean_sum {A : Type} [Fintype A]
    (J : Finset ℕ) (f : ℕ → A → ℝ) :
    uniformMean (fun x => ∑ j ∈ J, f j x) = ∑ j ∈ J, uniformMean (f j) := by
  classical
  unfold uniformMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem S6_32bStatement_of_deps (h01 : S6_01aStatement) (h03 : S6_03Statement)
    (h04 : S6_04aStatement) : S6_32bStatement := by
  intro n q m D hn hq
  let J := Finset.Ico (D + 1) (m + 1)
  have hpoint (x : Hist n m) :
      kappaKind q (fun G e => highEdge G D e) (tupleGraph x) ≤
        2 * ∑ j ∈ J, kappaDegree q j (tupleGraph x) := by
    simpa [J] using graph_high_count h03 h04 hn hq (tupleGraph x)
      (tupleGraph_edgeCount x)
  have havg := (h01 (Hist n m)).mono _ _ hpoint
  change meanGraph (n := n) m (kappaKind q (fun G e => highEdge G D e)) ≤
    2 * ∑ j ∈ J, degreeMean n q m j
  unfold meanGraph at havg ⊢
  calc
    uniformMean (fun x : Hist n m =>
        kappaKind q (fun G e => highEdge G D e) (tupleGraph x)) ≤
        uniformMean (fun x : Hist n m =>
          2 * ∑ j ∈ J, kappaDegree q j (tupleGraph x)) := havg
    _ = 2 * ∑ j ∈ J, meanGraph (n := n) m (kappaDegree q j) := by
      calc
        _ = uniformMean (fun x : Hist n m =>
            ∑ j ∈ J, 2 * kappaDegree q j (tupleGraph x)) := by
          congr 1
          funext x
          rw [Finset.mul_sum]
        _ = ∑ j ∈ J, uniformMean (fun x : Hist n m =>
            2 * kappaDegree q j (tupleGraph x)) := uniformMean_sum J
              (fun j x => 2 * kappaDegree q j (tupleGraph x))
        _ = 2 * ∑ j ∈ J, meanGraph (n := n) m (kappaDegree q j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          exact (h01 (Hist n m)).smul 2 (fun x => kappaDegree q j (tupleGraph x))

end ThLean.W.S636


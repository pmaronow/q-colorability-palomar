import ThLean.BP.S6.Credit

noncomputable section
open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S625

private theorem noLoop_iff_not_isDiag {α : Type} [DecidableEq α]
    (z : Sym2 α) : (∀ v : α, z ≠ s(v, v)) ↔ ¬ z.IsDiag := by
  induction z using Sym2.ind with
  | h a b => simp [eq_comm]

private def pairNoDiagEquiv (n : ℕ) [DecidableEq (Fin n)] :
    Edge n ≃ {z : Sym2 (Fin n) // ¬ z.IsDiag} where
  toFun e := ⟨e.val, (noLoop_iff_not_isDiag e.val).mp e.property⟩
  invFun z := ⟨z.val, (noLoop_iff_not_isDiag z.val).mpr z.property⟩
  left_inv e := by cases e; rfl
  right_inv z := by cases z; rfl

private theorem edge_card (n : ℕ) [DecidableEq (Fin n)] :
    Fintype.card (Edge n) = n.choose 2 := by
  calc
    Fintype.card (Edge n) = Fintype.card {z : Sym2 (Fin n) // ¬ z.IsDiag} :=
      Fintype.card_congr (pairNoDiagEquiv n)
    _ = (Fintype.card (Fin n)).choose 2 := Sym2.card_subtype_not_diag
    _ = n.choose 2 := by simp

private theorem sum_split_univ {V : Type*} [Fintype V] [DecidableEq V]
    (C W : Finset V) (hcover : C ∪ W = Finset.univ)
    (hdisj : Disjoint C W) (f : V → ℝ) :
    (∑ x : V, f x) = (∑ x ∈ C, f x) + (∑ x ∈ W, f x) := by
  calc
    (∑ x : V, f x) = ∑ x ∈ C ∪ W, f x := by rw [← hcover]
    _ = (∑ x ∈ C, f x) + (∑ x ∈ W, f x) := Finset.sum_union hdisj

private theorem sum_offdiag_sub_diag {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) (d : V → V → ℝ) :
    (∑ a ∈ W, ∑ b ∈ W, if a ≠ b then d a b else 0) =
      (∑ a ∈ W, ∑ b ∈ W, d a b) - ∑ a ∈ W, d a a := by
  classical
  have hrow : ∀ a ∈ W,
      (∑ b ∈ W, if a ≠ b then d a b else 0) =
        (∑ b ∈ W, d a b) - d a a := by
    intro a ha
    have hfilter :
        (∑ b ∈ W, if a ≠ b then d a b else 0) = ∑ b ∈ W.erase a, d a b := by
      rw [← Finset.sum_filter]
      congr 1
      ext b
      simp [Finset.mem_erase, and_comm, eq_comm]
    have hsplit := Finset.add_sum_erase W (fun b => d a b) ha
    rw [hfilter]
    linarith
  calc
    (∑ a ∈ W, ∑ b ∈ W, if a ≠ b then d a b else 0) =
        ∑ a ∈ W, ((∑ b ∈ W, d a b) - d a a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hrow a ha
    _ = (∑ a ∈ W, ∑ b ∈ W, d a b) - ∑ a ∈ W, d a a := by
      rw [Finset.sum_sub_distrib]

private theorem credited_eq_at {n q : ℕ} (G : Graph n) (u : Fin n)
    (hsym : ∀ a b, creditedAt q G u a b = creditedAt q G u b a)
    (e : Edge n) (a b : Fin n) (he : e.val = s(a, b)) :
    credited q G u e = creditedAt q G u a b := by
  classical
  ext y
  simp only [credited, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a', b', hab, hy⟩
    have hpair : s(a', b') = s(a, b) := hab.symm.trans he
    rcases Sym2.eq_iff.mp hpair with hsame | hswap
    · rcases hsame with ⟨ha, hb⟩
      subst a'
      subst b'
      exact hy
    · rcases hswap with ⟨ha, hb⟩
      subst a'
      subst b'
      rw [hsym b a] at hy
      exact hy
  · intro hy
    exact ⟨a, b, he, hy⟩

theorem S6_24aStatement_of_deps
    (h03 : ThLean.BP.S6.S6_03Statement)
    (h05 : ThLean.BP.S6.S6_05Statement)
    (h17 : ThLean.BP.S6.S6_17Statement) :
    ThLean.BP.S6.S6_24aStatement := by
  classical
  intro n q hn hq G u hG
  let C : Finset (Fin n) := frozenClass q G u
  let W : Finset (Fin n) := Finset.univ \ C
  let sect (a : Fin n) : ℝ :=
    min (((relationSection q G u a).card : ℝ) / (C.card : ℝ)) 1
  let direct (a b : Fin n) : ℝ := by
    letI : DecidableEq (Fin n) := Classical.decEq _
    exact min (((relationSection q G u a ∩ relationSection q G u b).card : ℝ) /
      (C.card : ℝ)) 1
  let term (a b : Fin n) : ℝ :=
    if a ≠ b then min (((creditedAt q G u a b).card : ℝ) / (C.card : ℝ)) 1 else 0
  have h05n := h05 n q hn hq G u
  rcases h05n with ⟨_, _, _, hsecC, _, _, _, hclass, _⟩
  have hclass' := hclass hG
  have hCpos : 0 < (C.card : ℝ) := by
    have hNat : 0 < C.card := by
      unfold C
      omega
    exact_mod_cast hNat
  have hcover : C ∪ W = (Finset.univ : Finset (Fin n)) := by
    ext a
    simp [W]
  have hdisj : Disjoint C W := by
    simp [W, Finset.disjoint_left]
  have h17n := h17 n q hn hq G u
  rcases h17n with ⟨hcreditSym, _, _⟩
  let hSym : Sym2 (Fin n) → ℝ :=
    Sym2.lift ⟨fun a b =>
      min (((creditedAt q G u a b).card : ℝ) / (C.card : ℝ)) 1,
      fun a b => by
        change min (((creditedAt q G u a b).card : ℝ) / (C.card : ℝ)) 1 =
          min (((creditedAt q G u b a).card : ℝ) / (C.card : ℝ)) 1
        rw [hcreditSym a b]⟩
  have hcreditMean :
      uniformMean (fun e : Edge n =>
        min (((credited q G u e).card : ℝ) / (C.card : ℝ)) 1) =
      uniformMean (fun e : Edge n => hSym e.val) := by
    apply congrArg uniformMean
    funext e
    let ab : Fin n × Fin n := Classical.choose (Sym2.mk_surjective e.val)
    have hab : s(ab.1, ab.2) = e.val := Classical.choose_spec (Sym2.mk_surjective e.val)
    have heq := credited_eq_at G u hcreditSym e ab.1 ab.2 hab.symm
    have hsymEq : hSym e.val = hSym (s(ab.1, ab.2)) :=
      (congrArg hSym hab).symm
    rw [hsymEq]
    simp only [hSym, Sym2.lift_mk]
    rw [congrArg Finset.card heq]
  have hmean := (h03 n hn).2.1 hSym
  have hpairCount : 2 * (Fintype.card (Edge n) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    rw [edge_card]
    rw [Nat.cast_choose_two]
    ring
  have hsecEmpty : ∀ a ∈ C, relationSection q G u a = ∅ := by
    intro a ha
    exact hsecC a (by simpa [C] using ha)
  have htermCC : ∀ a ∈ C, ∀ b ∈ C, term a b = 0 := by
    intro a ha b hb
    have hfa : Frozen q G u a := by simpa [C, frozenClass] using ha
    have hfb : Frozen q G u b := by simpa [C, frozenClass] using hb
    simp [term, creditedAt, hG, hfa, hfb]
  have htermCW : ∀ a ∈ C, ∀ b ∈ W, term a b = sect b := by
    intro a ha b hb
    have hfa : Frozen q G u a := by simpa [C, frozenClass] using ha
    have hfb : ¬ Frozen q G u b := by simpa [W, C, frozenClass] using hb
    have hab : a ≠ b := by
      intro heq
      subst b
      exact hfb hfa
    simp [term, sect, creditedAt, hG, hfa, hfb, hab]
  have htermWC : ∀ a ∈ W, ∀ b ∈ C, term a b = sect a := by
    intro a ha b hb
    have hfa : ¬ Frozen q G u a := by simpa [W, C, frozenClass] using ha
    have hfb : Frozen q G u b := by simpa [C, frozenClass] using hb
    have hab : a ≠ b := by
      intro heq
      subst b
      exact hfa hfb
    simp [term, sect, creditedAt, hG, hfa, hfb, hab]
  have htermWW : ∀ a ∈ W, ∀ b ∈ W, term a b =
      if a ≠ b then direct a b else 0 := by
    intro a ha b hb
    have hfa : ¬ Frozen q G u a := by simpa [W, C, frozenClass] using ha
    have hfb : ¬ Frozen q G u b := by simpa [W, C, frozenClass] using hb
    by_cases hab : a = b <;> simp [term, direct, creditedAt, hG, hfa, hfb, hab]
  have hpartition :
      (∑ a : Fin n, ∑ b : Fin n, term a b) =
        directCreditSum q G u +
          (2 * (C.card : ℝ) - 1) *
            sectionMass (relation q G u) C.card := by
    have houter := sum_split_univ C W hcover hdisj (fun a => ∑ b : Fin n, term a b)
    have hinner (a : Fin n) :
        (∑ b : Fin n, term a b) = (∑ b ∈ C, term a b) + (∑ b ∈ W, term a b) :=
      sum_split_univ C W hcover hdisj (term a)
    have hrowC : ∀ a ∈ C, (∑ b : Fin n, term a b) = ∑ b ∈ W, sect b := by
      intro a ha
      rw [hinner a]
      have hcc : (∑ b ∈ C, term a b) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        exact htermCC a ha b hb
      have hcw : (∑ b ∈ W, term a b) = ∑ b ∈ W, sect b := by
        apply Finset.sum_congr rfl
        intro b hb
        exact htermCW a ha b hb
      rw [hcc, hcw, zero_add]
    have hrowW : ∀ a ∈ W,
        (∑ b : Fin n, term a b) = (C.card : ℝ) * sect a +
          ∑ b ∈ W, if a ≠ b then direct a b else 0 := by
      intro a ha
      rw [hinner a]
      have hwc : (∑ b ∈ C, term a b) = (C.card : ℝ) * sect a := by
        calc
          (∑ b ∈ C, term a b) = ∑ b ∈ C, sect a := by
            apply Finset.sum_congr rfl
            intro b hb
            exact htermWC a ha b hb
          _ = (C.card : ℝ) * sect a := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hww : (∑ b ∈ W, term a b) =
          ∑ b ∈ W, if a ≠ b then direct a b else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact htermWW a ha b hb
      rw [hwc, hww]
    have houterC :
        (∑ a ∈ C, ∑ b : Fin n, term a b) = ∑ a ∈ C, ∑ b ∈ W, sect b := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hrowC a ha
    have houterW :
        (∑ a ∈ W, ∑ b : Fin n, term a b) =
          ∑ a ∈ W, ((C.card : ℝ) * sect a +
            ∑ b ∈ W, if a ≠ b then direct a b else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hrowW a ha
    have hcross :
        (∑ a ∈ C, ∑ b ∈ W, sect b) =
          (C.card : ℝ) * (∑ b ∈ W, sect b) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hcross' :
        (∑ a ∈ W, (C.card : ℝ) * sect a) =
          (C.card : ℝ) * (∑ a ∈ W, sect a) := by
      rw [Finset.mul_sum]
    have hsection :
        sectionMass (relation q G u) C.card = ∑ a ∈ W, sect a := by
      unfold sectionMass
      rw [sum_split_univ C W hcover hdisj]
      have hzero :
          (∑ a ∈ C,
            min (((sectionOf (relation q G u) a).card : ℝ) / (C.card : ℝ)) 1) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        rw [show sectionOf (relation q G u) a = relationSection q G u a from rfl,
          hsecEmpty a ha]
        simp
      rw [hzero, zero_add]
      apply Finset.sum_congr rfl
      intro a ha
      rw [show sectionOf (relation q G u) a = relationSection q G u a from rfl]
    have hdirect :
        directCreditSum q G u = ∑ a ∈ W, ∑ b ∈ W, direct a b := by
      simp [directCreditSum, direct, C, W]
    rw [houter, houterC, houterW, Finset.sum_add_distrib]
    rw [sum_offdiag_sub_diag W direct]
    rw [hcross, hcross']
    have hdiag : ∑ a ∈ W, direct a a = ∑ a ∈ W, sect a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [direct, sect]
    rw [hdiag, ← hdirect, ← hsection]
    ring
  have hordered :
      (∑ a : Fin n, ∑ b : Fin n,
        indicator (a ≠ b) * hSym (s(a, b))) =
        directCreditSum q G u +
          (2 * (C.card : ℝ) - 1) *
            sectionMass (relation q G u) C.card := by
    simpa [term, hSym, Sym2.lift_mk, indicator] using hpartition
  change (2 * (Fintype.card (Edge n) : ℝ)) *
      uniformMean (fun e : Edge n =>
        min (((credited q G u e).card : ℝ) / (C.card : ℝ)) 1) =
    directCreditSum q G u + (2 * (C.card : ℝ) - 1) *
      sectionMass (relation q G u) C.card
  rw [hcreditMean]
  rw [hmean]
  rw [hordered]
  rw [hpairCount]
  have hNm1 : (n : ℝ) - 1 ≠ 0 := by
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  field_simp [hNm1] <;> ring

end ThLean.W.S625

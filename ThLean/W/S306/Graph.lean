import ThLean.BP.S3.Graph

noncomputable section

open scoped BigOperators

namespace ThLean.W.S306

open ThresholdFoundations

private theorem pair_rep {V : Type*} (e : Pair V) :
    ∃ u v, e.val = s(u, v) ∧ u ≠ v := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
    by_cases huv : u = v
    · subst v
      exact False.elim (he u rfl)
    · exact ⟨u, v, rfl, huv⟩

private theorem frozen_symm {V : Type*} [Fintype V] {q : ℕ}
    {G : MGraph V} {u v : V} (h : Frozen q G u v) : Frozen q G v u := by
  rcases h with ⟨hc, hall⟩
  exact ⟨hc, fun σ hσ => (hall σ hσ).symm⟩

private theorem frozenPair_iff_frozen {V : Type*} [Fintype V] {q : ℕ}
    {G : MGraph V} (e : Pair V) {u v : V} (hev : e.val = s(u, v)) :
    FrozenPair q G e ↔ Frozen q G u v := by
  constructor
  · rintro ⟨a, b, hab, hfr⟩
    have hEq : s(a, b) = s(u, v) := hab.symm.trans hev
    rcases Sym2.eq_iff.mp hEq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
    · simpa [hau, hbv] using hfr
    · have hfr' : Frozen q G v u := by simpa [hav, hbu] using hfr
      exact frozen_symm hfr'
  · intro hfr
    exact ⟨u, v, hev, hfr⟩

private theorem pair_mk_proof {V : Type*} {u v : V} (huv : u ≠ v) :
    ∀ x : V, s(u, v) ≠ s(x, x) := by
  intro x hdiag
  rcases Sym2.eq_iff.mp hdiag with ⟨hux, hvx⟩ | ⟨hux, hvx⟩
  · exact huv (hux.trans hvx.symm)
  · exact huv (hux.trans hvx.symm)

private theorem addPair_coloring_iff {V : Type*} {q : ℕ}
    (G : MGraph V) (e : Pair V) {u v : V} (hev : e.val = s(u, v))
    (σ : V → Fin q) :
    IsColoring q (addPair G e) σ ↔ IsColoring q G σ ∧ σ u ≠ σ v := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b hab
      have hmono : G (s(a, b)) ≤ addPair G e (s(a, b)) := by
        change G (s(a, b)) ≤ Function.update G e.val (G e.val + 1) (s(a, b))
        by_cases heq : s(a, b) = e.val
        · rw [heq, Function.update_self]
          omega
        · rw [Function.update_of_ne heq]
      exact h a b (lt_of_lt_of_le hab hmono)
    · have hpos : 0 < addPair G e (s(u, v)) := by
        change 0 < Function.update G e.val (G e.val + 1) (s(u, v))
        rw [← hev, Function.update_self]
        omega
      exact h u v hpos
  · rintro ⟨hG, hneq⟩ a b hab
    by_cases heq : s(a, b) = e.val
    · have hEq : s(a, b) = s(u, v) := heq.trans hev
      rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hneq
      · exact hneq.symm
    · have habG : 0 < G (s(a, b)) := by
        have hval : addPair G e (s(a, b)) = G (s(a, b)) := by
          change Function.update G e.val (G e.val + 1) (s(a, b)) = G (s(a, b))
          exact Function.update_of_ne heq _ _
        rw [hval] at hab
        exact hab
      exact hG a b habG

theorem S3_10Statement_holds : ThLean.BP.S3.S3_10Statement := by
  classical
  intro V _ q _ _
  have hAdd : ∀ (G : MGraph V) (e : Pair V),
      Colorable q (addPair G e) ↔ Colorable q G ∧ ¬ FrozenPair q G e := by
    intro G e
    obtain ⟨u, v, hev, _huv⟩ := pair_rep e
    constructor
    · rintro ⟨σ, hσ⟩
      have ⟨hG, hneq⟩ := (addPair_coloring_iff G e hev σ).mp hσ
      refine ⟨⟨σ, hG⟩, ?_⟩
      intro hfr
      have hfr' := (frozenPair_iff_frozen e hev).mp hfr
      exact hneq (hfr'.2 σ hG)
    · rintro ⟨⟨σ, hG⟩, hnot⟩
      have hnotFrozen : ¬ Frozen q G u v := by
        intro hfr
        exact hnot ((frozenPair_iff_frozen e hev).mpr hfr)
      have hex : ∃ τ, IsColoring q G τ ∧ τ u ≠ τ v := by
        by_contra h
        apply hnotFrozen
        refine ⟨⟨σ, hG⟩, ?_⟩
        intro τ hτ
        by_contra hneq
        exact h ⟨τ, hτ, hneq⟩
      rcases hex with ⟨τ, hτ, hneq⟩
      exact ⟨τ, (addPair_coloring_iff G e hev τ).mpr ⟨hτ, hneq⟩⟩

  refine ⟨hAdd, ?_, ?_, ?_⟩
  · intro G
    have hp : ∀ e : Pair V,
        (Colorable q G ∧ ¬ Colorable q (addPair G e)) ↔ FrozenPair q G e := by
      intro e
      by_cases hc : Colorable q G
      · constructor
        · rintro ⟨_, hna⟩
          by_contra hnf
          exact hna ((hAdd G e).2 ⟨hc, hnf⟩)
        · intro hf
          refine ⟨hc, ?_⟩
          intro ha
          exact ((hAdd G e).mp ha).2 hf
      · simp [hc, FrozenPair, Frozen]
    have hfun :
        (fun e : Pair V => Colorable q G ∧ ¬ Colorable q (addPair G e)) =
          FrozenPair q G := funext fun e => propext (hp e)
    change uniformProb (fun e : Pair V =>
      Colorable q G ∧ ¬ Colorable q (addPair G e)) = uniformProb (FrozenPair q G)
    rw [hfun]
  · intro G e hG hpos hfr
    rcases hfr with ⟨u, v, hev, hFrozen⟩
    rcases hG with ⟨σ, hσ⟩
    have hpos' : 0 < G (s(u, v)) := by simpa [hev] using hpos
    have hneq : σ u ≠ σ v := hσ u v hpos'
    exact hneq (hFrozen.2 σ hσ)
  · intro G u
    unfold inFrozenPair
    constructor
    · rintro ⟨e, ht, hfr⟩
      rcases ht with ⟨v, huv⟩
      rcases hfr with ⟨a, b, hab, hFrozen⟩
      have hEq : s(a, b) = s(u, v) := hab.symm.trans huv
      have huv_ne : u ≠ v := by
        intro huv_eq
        subst v
        exact e.property u huv
      have hFrozenUV : Frozen q G u v := by
        rcases Sym2.eq_iff.mp hEq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
        · simpa [hau, hbv] using hFrozen
        · have hFrozenVU : Frozen q G v u := by simpa [hav, hbu] using hFrozen
          exact frozen_symm hFrozenVU
      have hSelf : Frozen q G u u := ⟨hFrozenUV.1, fun _ _ => rfl⟩
      have huMem : u ∈ frozenClass q G u := by
        simp only [frozenClass, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hSelf
      have hvMem : v ∈ frozenClass q G u := by
        simp only [frozenClass, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hFrozenUV
      have hcard : 1 < (frozenClass q G u).card :=
        Finset.one_lt_card_iff.mpr ⟨u, v, huMem, hvMem, huv_ne⟩
      omega
    · intro hcard
      have hcard' : 1 < (frozenClass q G u).card := by omega
      rcases Finset.one_lt_card_iff.mp hcard' with ⟨a, b, ha, hb, hab⟩
      have hFrozenA : Frozen q G u a := (Finset.mem_filter.mp ha).2
      have hFrozenB : Frozen q G u b := (Finset.mem_filter.mp hb).2
      by_cases hau : a = u
      · subst a
        refine ⟨⟨s(u, b), pair_mk_proof hab⟩, ⟨b, rfl⟩, ⟨u, b, rfl, hFrozenB⟩⟩
      · refine ⟨⟨s(u, a), pair_mk_proof (Ne.symm hau)⟩, ⟨a, rfl⟩, ⟨u, a, rfl, hFrozenA⟩⟩

example : ThLean.BP.S3.S3_10Statement := S3_10Statement_holds

end ThLean.W.S306

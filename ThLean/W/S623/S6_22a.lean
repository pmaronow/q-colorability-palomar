import ThLean.BP.S6.Credit

noncomputable section
open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S623

private theorem sum_univ_eq_compl_of_zero {α : Type} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (hz : ∀ x ∈ s, f x = 0) :
    (∑ x : α, f x) = ∑ x ∈ Finset.univ \ s, f x := by
  classical
  symm
  apply Finset.sum_subset Finset.sdiff_subset
  intro x hx hxnot
  have hs : x ∈ s := by
    by_contra h
    exact hxnot (Finset.mem_sdiff.mpr ⟨hx, h⟩)
  exact hz x hs

theorem S6_22aStatement_holds : ThLean.BP.S6.S6_22aStatement := by
  classical
  intro n q hn hq G u hG
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  let C := frozenClass q G u
  let W := Finset.univ \ C
  have hsection_empty : ∀ a, a ∈ C → relationSection q G u a = ∅ := by
    intro a ha
    apply Finset.ext
    intro v
    constructor
    · intro hv
      have hrel : (a, v) ∈ relation q G u := (Finset.mem_filter.mp hv).2
      have hparts := (Finset.mem_filter.mp hrel).2
      have hnot : ¬ Frozen q G u a := hparts.2.1
      have hfr : Frozen q G u a := (Finset.mem_filter.mp ha).2
      exact (hnot hfr).elim
    · intro hv
      cases hv
  have hsection_eq : ∀ a, sectionOf (relation q G u) a = relationSection q G u a := by
    intro a
    rfl
  constructor
  · let f : Fin n → Fin n → ℝ := fun a b =>
      min (((sectionOf (relation q G u) a ∩ sectionOf (relation q G u) b).card : ℝ) /
        (C.card : ℝ)) 1
    change (∑ a : Fin n, ∑ b : Fin n, f a b) =
      ∑ a ∈ W, ∑ b ∈ W, f a b
    have hb : ∀ a, (∑ b : Fin n, f a b) = ∑ b ∈ W, f a b := by
      intro a
      apply sum_univ_eq_compl_of_zero C (f a)
      intro b hb
      simp [f, hsection_eq, hsection_empty b hb]
    calc
      (∑ a : Fin n, ∑ b : Fin n, f a b) =
          ∑ a : Fin n, ∑ b ∈ W, f a b := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hb a
      _ = ∑ a ∈ W, ∑ b ∈ W, f a b := by
        apply sum_univ_eq_compl_of_zero C (fun a => ∑ b ∈ W, f a b)
        intro a ha
        simp [f, hsection_eq, hsection_empty a ha]
  · let g : Fin n → ℝ := fun a =>
      min (((relationSection q G u a).card : ℝ) / (C.card : ℝ)) 1
    have hsum : (∑ a : Fin n, g a) = ∑ a ∈ W, g a := by
      apply sum_univ_eq_compl_of_zero C g
      intro a ha
      simp [g, hsection_empty a ha]
    change 2 * ((C.card : ℝ) - 1) *
      (∑ a : Fin n, g a) = 2 * ((C.card : ℝ) - 1) * ∑ a ∈ W, g a
    rw [hsum]

end ThLean.W.S623

import ThLean.Defs.Bridge

noncomputable section
open scoped BigOperators

namespace ThLean.W.BR02

open ThresholdFoundations

private lemma prefix_mem_iff {n m : ℕ} (x : ThresholdChallenge.EdgePrefix n m)
    (p : ThresholdChallenge.Pair n) :
    p ∈ ThresholdChallenge.prefixMultigraph x ↔ ∃ i : Fin m, x i = p := by
  simp [ThresholdChallenge.prefixMultigraph]

private lemma tupleGraph_pos_iff {n m : ℕ} (x : ThresholdChallenge.EdgePrefix n m)
    (f : ThresholdChallenge.Pair n → ThresholdFoundations.Pair (Fin n))
    (e : Sym2 (Fin n)) :
    0 < ThresholdFoundations.tupleGraph (f ∘ x) e ↔ ∃ i : Fin m, (f (x i)).val = e := by
  classical
  unfold ThresholdFoundations.tupleGraph
  simp only [Function.comp_apply]
  constructor
  · intro h
    have hn : (Finset.univ.filter (fun i : Fin m => (f (x i)).val = e)).Nonempty :=
      Finset.card_pos.mp h
    rcases hn with ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩
    apply Finset.card_pos.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

private lemma sum_if_const {α : Type*} [Fintype α] (P : Prop) [Decidable P]
    (g : α → ℕ) :
    (if P then ∑ a, g a else 0) = ∑ a, if P then g a else 0 := by
  by_cases h : P <;> simp [h]

 theorem ColoringBridgeStatement_holds : ThresholdFoundations.ColoringBridgeStatement := by
  classical
  constructor
  · intro q n m f hf x
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      apply Finset.card_eq_zero.mpr
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro heq
        exact False.elim ((f (x i)).property v heq)
      · intro hi
        simp at hi
    · unfold ThresholdFoundations.edgeCount ThresholdFoundations.tupleGraph
      simp only [Function.comp_apply]
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_ite_eq]
      simp
    · constructor
      · rintro ⟨σ, hσ⟩
        refine ⟨σ, ?_⟩
        intro u v huv
        rcases (tupleGraph_pos_iff x f (s(u, v))).mp huv with ⟨i, hi⟩
        apply hσ (x i)
        · exact (prefix_mem_iff x (x i)).2 ⟨i, rfl⟩
        · exact ((hf (x i)).symm).trans hi
      · rintro ⟨σ, hσ⟩
        refine ⟨σ, ?_⟩
        intro p hp u v huv
        rcases (prefix_mem_iff x p).mp hp with ⟨i, rfl⟩
        apply hσ u v
        exact (tupleGraph_pos_iff x f (s(u, v))).mpr ⟨i, (hf (x i)).trans huv⟩
    · intro a
      unfold ThresholdFoundations.degree ThresholdFoundations.tupleGraph
      simp only [Function.comp_apply]
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      calc
        (∑ e : Sym2 (Fin n), if Touches a e then
          ∑ i : Fin m, if (f (x i)).val = e then 1 else 0 else 0) =
            ∑ e, ∑ i, if Touches a e then
              (if (f (x i)).val = e then 1 else 0) else 0 := by
                apply Finset.sum_congr rfl
                intro e he
                exact sum_if_const (Touches a e) (fun i => if (f (x i)).val = e then 1 else 0)
        _ = ∑ i : Fin m, ∑ e : Sym2 (Fin n), if Touches a e then
              (if (f (x i)).val = e then 1 else 0) else 0 := Finset.sum_comm
        _ = ∑ i : Fin m, if Touches a (x i).val then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hf (x i)]
              calc
                (∑ e : Sym2 (Fin n), if Touches a e then
                  (if (x i).val = e then 1 else 0) else 0) =
                    ∑ e, if (x i).val = e then
                      (if Touches a (x i).val then 1 else 0) else 0 := by
                      apply Finset.sum_congr rfl
                      intro e he
                      by_cases h : (x i).val = e <;> simp [h]
                _ = if Touches a (x i).val then 1 else 0 := by
                      rw [Finset.sum_ite_eq]
                      simp
  · intro q n E hE
    constructor
    · rintro ⟨σ, hσ⟩
      refine ⟨σ, ?_⟩
      intro u v huv
      apply hσ u v
      by_contra hmem
      have : ¬ 0 < ThresholdFoundations.simpleGraph E (s(u, v)) := by
        simp [ThresholdFoundations.simpleGraph, hmem]
      exact this huv
    · rintro ⟨σ, hσ⟩
      refine ⟨σ, ?_⟩
      intro u v huv
      apply hσ u v
      simp [ThresholdFoundations.simpleGraph, huv]

example : ThresholdFoundations.ColoringBridgeStatement := ColoringBridgeStatement_holds

end ThLean.W.BR02

import ThLean.BP.SA.Interpolation

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA34

open ThresholdFoundations

private lemma card_inter_real_as_sum (V : Type) [Fintype V] (C T : Finset V) :
    ((C ∩ T).card : ℝ) = ∑ x ∈ T, indicator (x ∈ C) := by
  classical
  letI : DecidablePred (fun x => x ∈ C) := fun x => Classical.propDecidable _
  have hset : T.filter (fun x => x ∈ C) = C ∩ T := by
    ext x
    simp [and_comm]
  calc
    ((C ∩ T).card : ℝ) = ((T.filter (fun x => x ∈ C)).card : ℝ) := by rw [hset]
    _ = ∑ x ∈ T, indicator (x ∈ C) := by
      have h := congrArg (fun n : ℕ => (n : ℝ))
        (Finset.card_filter (fun x => x ∈ C) T)
      simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        indicator] using h

private lemma frozenClass_eq_of_frozen {V : Type} [Fintype V]
    (q : ℕ) (G : MGraph V) (hrel : Equivalence (Frozen q G))
    {x y : V} (hxy : Frozen q G x y) :
    frozenClass q G x = frozenClass q G y := by
  ext z
  simp only [frozenClass, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hxz
    exact hrel.trans (hrel.symm hxy) hxz
  · intro hyz
    exact hrel.trans hxy hyz

private lemma frozen_pair_of_common_class {V : Type} [Fintype V]
    (q : ℕ) (G : MGraph V) (hrel : Equivalence (Frozen q G))
    (C : Finset V) (hC : C ∈ frozenClasses q G) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C) :
    Frozen q G x y ∧ C = frozenClass q G x := by
  classical
  rcases Finset.mem_filter.mp hC with ⟨himage, _⟩
  rcases Finset.mem_image.mp himage with ⟨z, _, hCz⟩
  have hxz : Frozen q G z x := by
    rw [← hCz] at hx
    simpa [frozenClass] using hx
  have hyz : Frozen q G z y := by
    rw [← hCz] at hy
    simpa [frozenClass] using hy
  exact ⟨hrel.trans (hrel.symm hxz) hyz,
    hCz.symm.trans (frozenClass_eq_of_frozen q G hrel hxz)⟩

private lemma frozen_pair_indicator_sum {V : Type} [Fintype V]
    (q : ℕ) (G : MGraph V) (hrel : Equivalence (Frozen q G)) (x y : V) :
    (∑ C ∈ frozenClasses q G, indicator (x ∈ C ∧ y ∈ C)) =
      indicator (Frozen q G x y) := by
  classical
  letI : DecidablePred (fun C : Finset V => x ∈ C ∧ y ∈ C) :=
    fun C => Classical.propDecidable _
  have hsum := congrArg (fun n : ℕ => (n : ℝ))
    (Finset.card_filter (fun C : Finset V => x ∈ C ∧ y ∈ C)
      (frozenClasses q G))
  have hsum' :
      (∑ C ∈ frozenClasses q G, indicator (x ∈ C ∧ y ∈ C)) =
        ((frozenClasses q G).filter (fun C => x ∈ C ∧ y ∈ C)).card := by
    -- The natural-number filter count is the same finite sum of zeroes and ones.
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      indicator] using hsum.symm
  by_cases hxy : Frozen q G x y
  · have hx : x ∈ frozenClass q G x := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel.refl x⟩
    have hy : y ∈ frozenClass q G x :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    have hclass : frozenClass q G x ∈ frozenClasses q G := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, ?_⟩
      exact ⟨x, hx⟩
    have hfilter :
        (frozenClasses q G).filter (fun C => x ∈ C ∧ y ∈ C) =
          {frozenClass q G x} := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hC, hxyC⟩
        exact (frozen_pair_of_common_class q G hrel C hC hxyC.1 hxyC.2).2
      · rintro rfl
        exact ⟨hclass, ⟨hx, hy⟩⟩
    rw [hsum', hfilter]
    simp [indicator, hxy]
  · have hfilter :
        (frozenClasses q G).filter (fun C => x ∈ C ∧ y ∈ C) = ∅ := by
      ext C
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨hC, hxC, hyC⟩
      exact hxy (frozen_pair_of_common_class q G hrel C hC hxC hyC).1
    rw [hsum', hfilter]
    simp [indicator, hxy]

private lemma frozen_class_card_square_as_pairs {V : Type} [Fintype V]
    (C T : Finset V) :
    ((C ∩ T).card : ℝ) ^ 2 =
      ∑ x ∈ T, ∑ y ∈ T, indicator (x ∈ C ∧ y ∈ C) := by
  classical
  rw [pow_two]
  simp_rw [card_inter_real_as_sum]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxC : x ∈ C <;> by_cases hyC : y ∈ C <;>
    simp [indicator, hxC, hyC]

private lemma frozen_ordered_pair_count {V : Type} [Fintype V]
    (q : ℕ) (G : MGraph V) (T : Finset V)
    (hrel : Equivalence (Frozen q G)) :
    (∑ x ∈ T, ∑ y ∈ T, indicator (Frozen q G x y)) =
      ∑ C ∈ frozenClasses q G, ((C ∩ T).card : ℝ) ^ 2 := by
  classical
  calc
    (∑ x ∈ T, ∑ y ∈ T, indicator (Frozen q G x y)) =
        ∑ x ∈ T, ∑ y ∈ T,
          ∑ C ∈ frozenClasses q G, indicator (x ∈ C ∧ y ∈ C) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact (frozen_pair_indicator_sum q G hrel x y).symm
    _ = ∑ x ∈ T, ∑ C ∈ frozenClasses q G,
          ∑ y ∈ T, indicator (x ∈ C ∧ y ∈ C) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ C ∈ frozenClasses q G, ∑ x ∈ T,
          ∑ y ∈ T, indicator (x ∈ C ∧ y ∈ C) := by
      exact Finset.sum_comm
    _ = ∑ C ∈ frozenClasses q G, ((C ∩ T).card : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro C hC
      exact (frozen_class_card_square_as_pairs C T).symm

private lemma addEdge_colorable_implies_colorable {V : Type} [Fintype V]
    (q : ℕ) (G : MGraph V) (e : Sym2 V) :
    Colorable q (addEdge G e) → Colorable q G := by
  rintro ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro x y hxy
  apply hσ x y
  have hle : G (s(x, y)) ≤ addEdge G e (s(x, y)) := by
    by_cases he : s(x, y) = e
    · subst e
      simp [addEdge]
    · simp [addEdge, he]
  exact lt_of_lt_of_le hxy hle

theorem SA_I14bStatement_of_deps
    (h14a : ThLean.BP.SA.SA_I14aStatement) :
    ThLean.BP.SA.SA_I14bStatement := by
  classical
  intro V inst q G T hq
  by_cases hcolor : Colorable q G
  · obtain ⟨hrel, _, hadd⟩ := h14a V q G hq hcolor
    have hpoint (x y : V) :
        indicator (Colorable q G) -
            indicator (Colorable q (addEdge G s(x, y))) =
          indicator (Frozen q G x y) := by
      have hcriterion := hadd x y
      by_cases hadded : Colorable q (addEdge G s(x, y))
      · have hnotFrozen : ¬ Frozen q G x y := by
          intro hfrozen
          exact (hcriterion.mpr hfrozen) hadded
        simp [indicator, hcolor, hadded, hnotFrozen]
      · have hfrozen : Frozen q G x y := hcriterion.mp hadded
        simp [indicator, hcolor, hadded, hfrozen]
    calc
      (∑ x ∈ T, ∑ y ∈ T,
          (indicator (Colorable q G) -
            indicator (Colorable q (addEdge G s(x, y))))) =
          ∑ x ∈ T, ∑ y ∈ T, indicator (Frozen q G x y) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact hpoint x y
      _ = if Colorable q G then
            ∑ C ∈ frozenClasses q G, ((C ∩ T).card : ℝ) ^ 2 else 0 := by
        simpa [hcolor] using frozen_ordered_pair_count q G T hrel
  · have hadded (x y : V) :
        ¬ Colorable q (addEdge G s(x, y)) := by
      intro h
      exact hcolor (addEdge_colorable_implies_colorable q G (s(x, y)) h)
    simp [indicator, hcolor, hadded]

example (h14a : ThLean.BP.SA.SA_I14aStatement) :
    ThLean.BP.SA.SA_I14bStatement := SA_I14bStatement_of_deps h14a

end ThLean.W.SA34

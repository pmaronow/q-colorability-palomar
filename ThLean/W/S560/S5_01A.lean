import ThLean.BP.S5.Structure

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S560
open ThresholdFoundations

variable {V : Type*}

private lemma mapGraph_some_some (B : MGraph V) [Fintype V] (u v : V) :
    mapGraph some B (s(some u, some v)) = B (s(u, v)) := by
  classical
  unfold mapGraph
  rw [Finset.sum_eq_single_of_mem (s(u, v)) (Finset.mem_univ _)]
  · simp
  · intro e _ hne
    by_cases hmap : Sym2.map some e = s(some u, some v)
    · have hinj : Function.Injective (Sym2.map (some : V → Option V)) :=
        Sym2.map.injective (by intro x y hxy; exact Option.some.inj hxy)
      have heq : e = s(u, v) := hinj (by simpa using hmap)
      exact (hne heq).elim
    · simp [hmap]

private lemma mapGraph_some_root_root (B : MGraph V) [Fintype V] :
    mapGraph some B (s((none : Option V), none)) = 0 := by
  classical
  unfold mapGraph
  apply Finset.sum_eq_zero
  intro e _
  induction e using Sym2.ind with
  | h a b => simp

private lemma mapGraph_some_root_vertex (B : MGraph V) [Fintype V] (v : V) :
    mapGraph some B (s((none : Option V), some v)) = 0 := by
  classical
  unfold mapGraph
  apply Finset.sum_eq_zero
  intro e _
  induction e using Sym2.ind with
  | h a b => simp

private lemma star_root_root (xs : List V) :
    ThresholdFoundations.star xs (s((none : Option V), none)) = 0 := by
  classical
  induction xs with
  | nil => simp [ThresholdFoundations.star]
  | cons a xs ih =>
    change List.count (s(none, none))
      (s(none, some a) :: (xs.map fun v => s(none, some v))) = 0
    change List.count (s(none, none)) (xs.map fun v => s(none, some v)) = 0 at ih
    rw [List.count_cons_of_ne (by simp)]
    exact ih

private lemma star_root_vertex (xs : List V) (v : V) :
    ThresholdFoundations.star xs (s((none : Option V), some v)) = xs.count v := by
  classical
  change List.count (s(none, some v)) (xs.map fun w => s(none, some w)) = xs.count v
  exact List.count_map_of_injective xs (fun w => s(none, some w)) (by
    intro a b hab
    have h := Sym2.eq_iff.mp hab
    rcases h with ⟨_, h⟩ | ⟨h, _⟩
    · exact Option.some.inj h
    · cases h) v

private lemma star_vertex_vertex (xs : List V) (u v : V) :
    ThresholdFoundations.star xs (s(some u, some v)) = 0 := by
  classical
  induction xs with
  | nil => simp [ThresholdFoundations.star]
  | cons a xs ih =>
    change List.count (s(some u, some v))
      (s(none, some a) :: (xs.map fun w => s(none, some w))) = 0
    change List.count (s(some u, some v)) (xs.map fun w => s(none, some w)) = 0 at ih
    rw [List.count_cons_of_ne (by simp)]
    exact ih

private lemma addRoot_some_some (B : MGraph V) [Fintype V] (xs : List V) (u v : V) :
    addRoot B xs (s(some u, some v)) = B (s(u, v)) := by
  simp [addRoot, mapGraph_some_some, star_vertex_vertex]

private lemma addRoot_root_root (B : MGraph V) [Fintype V] (xs : List V) :
    addRoot B xs (s((none : Option V), none)) = 0 := by
  simp [addRoot, mapGraph_some_root_root, star_root_root]

private lemma addRoot_root_vertex (B : MGraph V) [Fintype V] (xs : List V) (v : V) :
    addRoot B xs (s((none : Option V), some v)) = xs.count v := by
  simp [addRoot, mapGraph_some_root_vertex, star_root_vertex]

private lemma addRoot_vertex_root (B : MGraph V) [Fintype V] (xs : List V) (v : V) :
    addRoot B xs (s(some v, none)) = xs.count v := by
  rw [show s(some v, none) = s(none, some v) by
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)]
  exact addRoot_root_vertex B xs v

theorem S5_01AStatement_holds : ThLean.BP.S5.S5_01AStatement := by
  intro V _ q hq B xs τ
  constructor
  · intro h
    constructor
    · intro u v huv
      apply h (some u) (some v)
      rw [addRoot_some_some]
      exact huv
    · intro v hv
      apply h none (some v)
      rw [addRoot_root_vertex]
      exact List.count_pos_iff.mpr hv
  · rintro ⟨hB, hxs⟩ u v huv
    cases u with
    | none =>
      cases v with
      | none =>
        rw [addRoot_root_root] at huv
        omega
      | some v =>
        rw [addRoot_root_vertex] at huv
        exact hxs v (List.count_pos_iff.mp huv)
    | some u =>
      cases v with
      | none =>
        rw [addRoot_vertex_root] at huv
        exact (hxs u (List.count_pos_iff.mp huv)).symm
      | some v =>
        rw [addRoot_some_some] at huv
        exact hB u v huv

end ThLean.W.S560

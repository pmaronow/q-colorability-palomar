module

public import ThLean.W.S370S.Lists

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V]

def lengthOccurrenceEquiv (xs : List (Sym2 V)) {n : ℕ} (h : xs.length = n) :
    Fin n ≃ Occurrence (edgesGraph xs) :=
  (finCongr h.symm).trans (listOccurrenceEquiv xs)

theorem lengthOccurrenceEquiv_pair (xs : List (Sym2 V)) {n : ℕ}
    (h : xs.length = n) (i : Fin n) :
    (lengthOccurrenceEquiv xs h i).1 = xs[i.val]'(by omega) := rfl

def cyclePairs {n : ℕ} (hn : 0 < n) (v : Fin n → V) : List (Sym2 V) :=
  List.ofFn (fun i => s(v i, v ⟨(i.val+1)%n, Nat.mod_lt _ hn⟩))

def pathPairs {n : ℕ} (v : Fin (n+1) → V) : List (Sym2 V) :=
  List.ofFn (fun i : Fin n => s(v i.castSucc, v i.succ))

theorem realize_dumbbell {n₁ n₂ n₃ : ℕ} (h₁ : 2 ≤ n₁) (h₂ : 2 ≤ n₂)
    (v₁ : Fin n₁ → V) (v₂ : Fin n₂ → V) (w : Fin (n₃+1) → V)
    (hv₁ : Function.Injective v₁) (hv₂ : Function.Injective v₂)
    (hw : Function.Injective w)
    (hshape :
      (n₃ = 0 ∧ ((Finset.univ.image v₁) ∩ (Finset.univ.image v₂)).card = 1) ∨
      (1 ≤ n₃ ∧ Disjoint (Finset.univ.image v₁) (Finset.univ.image v₂) ∧
        w 0 ∈ Finset.univ.image v₁ ∧ w (Fin.last n₃) ∈ Finset.univ.image v₂ ∧
        (Finset.univ.image w) ∩ (Finset.univ.image v₁) = {w 0} ∧
        (Finset.univ.image w) ∩ (Finset.univ.image v₂) = {w (Fin.last n₃)})) :
    ExactDumbbell (edgesGraph
      (cyclePairs (by omega) v₁ ++ cyclePairs (by omega) v₂ ++ pathPairs w)) := by
  let xs := cyclePairs (by omega) v₁ ++ cyclePairs (by omega) v₂ ++ pathPairs w
  let E := lengthOccurrenceEquiv xs (n := n₁+n₂+n₃) (by
    simp [xs, cyclePairs, pathPairs, Nat.add_assoc])
  let i₁ (i : Fin n₁) : Fin (n₁+n₂+n₃) := ⟨i.val, by omega⟩
  let i₂ (i : Fin n₂) : Fin (n₁+n₂+n₃) := ⟨n₁+i.val, by omega⟩
  let i₃ (i : Fin n₃) : Fin (n₁+n₂+n₃) := ⟨n₁+n₂+i.val, by omega⟩
  have inj₁ : Function.Injective (fun i => E (i₁ i)) := by
    intro i j h
    have := congrArg Fin.val (E.injective h)
    apply Fin.ext
    exact this
  have inj₂ : Function.Injective (fun i => E (i₂ i)) := by
    intro i j h
    have hh := congrArg Fin.val (E.injective h)
    apply Fin.ext
    dsimp [i₂] at hh
    omega
  have inj₃ : Function.Injective (fun i => E (i₃ i)) := by
    intro i j h
    have hh := congrArg Fin.val (E.injective h)
    apply Fin.ext
    dsimp [i₃] at hh
    omega
  let c : OccurrenceCycle (edgesGraph xs) := {
    length := n₁, length_ge_two := h₁, vertex := v₁, edge := fun i => E (i₁ i)
    vertex_injective := hv₁, edge_injective := inj₁
    joins := by
      intro i
      rw [lengthOccurrenceEquiv_pair]
      simp [xs, i₁, cyclePairs, pathPairs, List.getElem_append, i.isLt,
        show i.val < n₁+n₂ by omega] }
  let d : OccurrenceCycle (edgesGraph xs) := {
    length := n₂, length_ge_two := h₂, vertex := v₂, edge := fun i => E (i₂ i)
    vertex_injective := hv₂, edge_injective := inj₂
    joins := by
      intro i
      rw [lengthOccurrenceEquiv_pair]
      simp [xs, i₂, cyclePairs, pathPairs, List.getElem_append,
        show n₁+i.val < n₁+n₂ by omega, show ¬ n₁+i.val < n₁ by omega] }
  let p : OccurrencePath (edgesGraph xs) := {
    length := n₃, vertex := w, edge := fun i => E (i₃ i)
    vertex_injective := hw, edge_injective := inj₃
    joins := by
      intro i
      rw [lengthOccurrenceEquiv_pair]
      simp [xs, i₃, cyclePairs, pathPairs, List.getElem_append,
        show ¬ n₁+n₂+i.val < n₁ by omega,
        show ¬ n₁+n₂+i.val-n₁ < n₂ by omega,
        show n₁+n₂+i.val-n₁-n₂ = i.val by omega]
      exact Or.inl ⟨rfl, rfl⟩ }
  have hdis : Disjoint (cycleOccurrences c) (cycleOccurrences d) := by
    apply Finset.disjoint_left.mpr
    intro o ho ho'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ho'
    have hh := congrArg Fin.val (E.injective (hi.trans hj.symm))
    dsimp [i₁, i₂] at hh
    omega
  have hpd : Disjoint (pathOccurrences p) (cycleOccurrences c ∪ cycleOccurrences d) := by
    apply Finset.disjoint_left.mpr
    intro o ho ho'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
    rcases Finset.mem_union.mp ho' with ho' | ho'
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ho'
      have hh := congrArg Fin.val (E.injective (hi.trans hj.symm))
      dsimp [i₁, i₃] at hh
      omega
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ho'
      have hh := congrArg Fin.val (E.injective (hi.trans hj.symm))
      dsimp [i₂, i₃] at hh
      omega
  have hcover : cycleOccurrences c ∪ cycleOccurrences d ∪ pathOccurrences p = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro o
    obtain ⟨i, rfl⟩ := E.surjective o
    by_cases hi : i.val < n₁
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨⟨i.val, hi⟩, Finset.mem_univ _, rfl⟩
    · by_cases hj : i.val < n₁+n₂
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨(⟨i.val-n₁, by omega⟩ : Fin n₂), Finset.mem_univ _, ?_⟩
        change E (i₂ _) = E i
        congr 1
        apply Fin.ext
        dsimp [i₂]
        omega
      · apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨(⟨i.val-(n₁+n₂), by omega⟩ : Fin n₃), Finset.mem_univ _, ?_⟩
        change E (i₃ _) = E i
        congr 1
        apply Fin.ext
        dsimp [i₃]
        omega
  refine ⟨c, d, hdis, ?_⟩
  rcases hshape with ⟨hz, hcard⟩ | ⟨hp, hv, ha, hb, hpa, hpb⟩
  · left
    refine ⟨hcard, ?_⟩
    have hpempty : pathOccurrences p = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro o ho
      obtain ⟨i, _, _⟩ := Finset.mem_image.mp ho
      have hi : i.val < n₃ := i.isLt
      omega
    simpa [hpempty] using hcover
  · right
    exact ⟨hv, p, w 0, w (Fin.last n₃), hp, ⟨rfl,rfl⟩,
      ha, hb, hpa, hpb, hpd, hcover⟩

end ThLean.W.S370S

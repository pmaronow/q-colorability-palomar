module

public import ThLean.W.S340S.Partition

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations hiding neighborList
open ThLean.BP.S3
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S340S
universe u

def blockSublist {V : Type u} [Fintype V] (S : Finset V)
    (j : SplitIndex S) (w : List (Pair V)) : List (Pair V) :=
  w.filter (fun e => blockLabel S e = j)

theorem filter_singleton {V : Type u} [Fintype V] (w : List (Pair V)) (p : Pair V) :
    w.filter (fun e => e = p) = List.replicate (listGraph w p.val) p := by
  have hall : ∀ e ∈ w.filter (fun e => e = p), e = p := by simp
  rw [ThLean.W.S339.list_eq_replicate_of_forall_mem_eq _ p hall]
  congr 2
  apply List.filter_congr
  intro e he
  simp only [Subtype.ext_iff]

theorem blockSublist_out {V : Type u} [Fintype V] (S : Finset V)
    (p : Pair (Outside S)) (w : List (Pair V)) :
    blockSublist S (.inl p) w =
      List.replicate (inducedGraph (listGraph w) (Finset.univ \ S) p.val)
        (liftPair (Finset.univ \ S) p) := by
  simpa [blockSublist, blockLabel_out_iff, inducedGraph] using
    filter_singleton w (liftPair (Finset.univ \ S) p)

theorem blockSublist_in {V : Type u} [Fintype V] (S : Finset V)
    (p : Pair (Inside S)) (w : List (Pair V)) :
    blockSublist S (.inr (.inl p)) w =
      List.replicate (inducedGraph (listGraph w) S p.val) (liftPair S p) := by
  simpa [blockSublist, blockLabel_in_iff, inducedGraph] using
    filter_singleton w (liftPair S p)

def neighborWord {V : Type u} [Fintype V] (S : Finset V) (a : Inside S)
    (ys : List V) (hy : ∀ v ∈ ys, v ∈ Finset.univ \ S) : List (Pair V) :=
  ys.attach.map (fun v => crossPair S a ⟨v.val,hy v.val v.property⟩)

@[simp] theorem neighborWord_length {V : Type u} [Fintype V] (S : Finset V)
    (a : Inside S) (ys : List V) (hy : ∀ v ∈ ys, v ∈ Finset.univ \ S) :
    (neighborWord S a ys hy).length = ys.length := by simp [neighborWord]

theorem neighborWord_val {V : Type u} [Fintype V] (S : Finset V)
    (a : Inside S) (ys : List V) (hy : ∀ v ∈ ys, v ∈ Finset.univ \ S) :
    (neighborWord S a ys hy).map Subtype.val = ys.map (fun v => s(a.val,v)) := by
  simp [neighborWord, List.map_map]

theorem neighborWord_label {V : Type u} [Fintype V] (S : Finset V)
    (a : Inside S) (ys : List V) (hy : ∀ v ∈ ys, v ∈ Finset.univ \ S) :
    ∀ e ∈ neighborWord S a ys hy, blockLabel S e = .inr (.inr a) := by
  intro e he
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp he
  exact blockLabel_cross S a _

theorem blockSublist_cross_map {V : Type u} [Fintype V] (S : Finset V)
    (a : Inside S) (w : List (Pair V)) :
    (blockSublist S (.inr (.inr a)) w).map Subtype.val =
      (neighborList a.val (Finset.univ \ S) w).map (fun v => s(a.val,v)) := by
  induction w with
  | nil => simp [blockSublist,neighborList]
  | cons e w ih =>
    by_cases he : ∃ v ∈ Finset.univ \ S, e.val = s(a.val,v)
    · have hl := (blockLabel_cross_iff_exists S e a).mpr he
      have hval := (Classical.choose_spec he).2
      simp only [blockSublist, List.filter_cons, hl, decide_true, ite_true,
        List.map_cons, neighborList, List.filterMap_cons, dif_pos he, List.cons.injEq]
      exact ⟨hval,ih⟩
    · have hl := mt (blockLabel_cross_iff_exists S e a).mp he
      simpa only [blockSublist, List.filter_cons, hl, decide_false,
        Bool.false_eq_true, ite_false, neighborList, List.filterMap_cons, dif_neg he] using ih

theorem blockSublist_cross_iff {V : Type u} [Fintype V] (S : Finset V)
    (a : Inside S) (w : List (Pair V)) (ys : List V)
    (hy : ∀ v ∈ ys, v ∈ Finset.univ \ S) :
    blockSublist S (.inr (.inr a)) w = neighborWord S a ys hy ↔
      neighborList a.val (Finset.univ \ S) w = ys := by
  rw [← (List.map_injective_iff.mpr (@Subtype.val_injective (Sym2 V) _)).eq_iff,
    blockSublist_cross_map, neighborWord_val]
  exact (List.map_injective_iff.mpr (Sym2.mkEmbedding a.val).injective).eq_iff

theorem neighborList_mem {V : Type u} [Fintype V] (a : V) (S : Finset V)
    (w : List (Pair V)) : ∀ v ∈ neighborList a S w, v ∈ S := by
  intro v hv
  obtain ⟨e,_,he⟩ := List.mem_filterMap.mp hv
  dsimp at he
  split at he
  next h =>
    have hh := (Classical.choose_spec h).1
    have hv' := Option.some.inj he
    exact hv' ▸ hh
  next h => contradiction

theorem induced_listGraph_loopless {V : Type u} [Fintype V]
    (S : Finset V) (w : List (Pair V)) : Loopless (inducedGraph (listGraph w) S) := by
  intro v
  exact ThLean.W.S339.listGraph_loop_zero w v.val

theorem loopless_ext {W : Type u} (G H : MGraph W) (hG : Loopless G) (hH : Loopless H)
    (h : ∀ e : Pair W, G e.val = H e.val) : G = H := by
  funext e
  by_cases hd : ∃ v, e = s(v,v)
  · obtain ⟨v,rfl⟩ := hd
    rw [hG v,hH v]
  · exact h ⟨e,fun v hv => hd ⟨v,hv⟩⟩

def blockWords {V : Type u} [Fintype V] (S : Finset V)
    (B : MGraph (Outside S)) (C : MGraph (Inside S))
    (ys : Inside S → List V) (hy : ∀ a v, v ∈ ys a → v ∈ Finset.univ \ S) :
    SplitIndex S → List (Pair V)
  | .inl p => List.replicate (B p.val) (liftPair (Finset.univ \ S) p)
  | .inr (.inl p) => List.replicate (C p.val) (liftPair S p)
  | .inr (.inr a) => neighborWord S a (ys a) (hy a)

theorem blockWords_label {V : Type u} [Fintype V] (S : Finset V)
    (B : MGraph (Outside S)) (C : MGraph (Inside S))
    (ys : Inside S → List V) (hy : ∀ a v, v ∈ ys a → v ∈ Finset.univ \ S) :
    ∀ j e, e ∈ blockWords S B C ys hy j → blockLabel S e = j := by
  rintro (p | p | a) e he
  · obtain ⟨_,rfl⟩ := List.mem_replicate.mp he
    exact blockLabel_lift_out S p
  · obtain ⟨_,rfl⟩ := List.mem_replicate.mp he
    exact blockLabel_lift_in S p
  · exact neighborWord_label S a (ys a) (hy a) e he

theorem blockWords_event {V : Type u} [Fintype V] (S : Finset V)
    (B : MGraph (Outside S)) (C : MGraph (Inside S))
    (hB : Loopless B) (hC : Loopless C)
    (ys : Inside S → List V) (hy : ∀ a v, v ∈ ys a → v ∈ Finset.univ \ S)
    (w : List (Pair V)) :
    (∀ j, blockSublist S j w = blockWords S B C ys hy j) ↔
      inducedGraph (listGraph w) (Finset.univ \ S) = B ∧
      inducedGraph (listGraph w) S = C ∧
      ∀ a, neighborList a.val (Finset.univ \ S) w = ys a := by
  constructor
  · intro h
    refine ⟨loopless_ext _ _ (induced_listGraph_loopless _ _) hB ?_,
      loopless_ext _ _ (induced_listGraph_loopless _ _) hC ?_, ?_⟩
    · intro p
      have hh := congrArg List.length (h (.inl p))
      simpa [blockSublist_out,blockWords] using hh
    · intro p
      have hh := congrArg List.length (h (.inr (.inl p)))
      simpa [blockSublist_in,blockWords] using hh
    · intro a
      exact (blockSublist_cross_iff S a w (ys a) (hy a)).mp (h (.inr (.inr a)))
  · rintro ⟨hb,hc,hn⟩ (p | p | a)
    · simp [blockSublist_out,blockWords,hb]
    · simp [blockSublist_in,blockWords,hc]
    · exact (blockSublist_cross_iff S a w (ys a) (hy a)).mpr (hn a)

end ThLean.W.S340S

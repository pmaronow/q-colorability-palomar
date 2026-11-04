module

public import ThLean.W.S390S.SplitGraph
public import ThLean.W.S390S.Discrete
public import ThLean.W.S302.S3_03a

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S390S
open ThresholdFoundations ThLean.BP.S3
universe u v
set_option maxHeartbeats 1000000

theorem relabel_injective {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) :
    Function.Injective (relabel e) := by
  intro G H h
  funext x
  have hh := congrFun h (Sym2.map e x)
  simpa only [relabel, ThLean.W.S391.mapGraph_embedding_apply e e.injective] using hh

theorem uniformMean_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : uniformMean (fun x => f (e x)) = uniformMean f := by
  unfold uniformMean
  rw [Fintype.sum_equiv e _ _ (by intro _; rfl), Fintype.card_congr e]

theorem poissonGraphMean_relabel {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (t : ℝ) (f : MGraph Y → ℝ) :
    poissonGraphMean t (fun G => f (relabel e G)) = poissonGraphMean t f := by
  unfold poissonGraphMean poissonMixture
  apply tsum_congr
  intro m
  congr 1
  simp only [ThLean.W.S391.relabel_tupleGraph]
  exact uniformMean_equiv (ThLean.W.S391.edgeTupleEquiv e m) (fun x => f (tupleGraph x))

theorem poissonGraphProb_relabel {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (t : ℝ) (G : MGraph X) :
    poissonGraphMean t (fun H => indicator (H = relabel e G)) =
      poissonGraphMean t (fun H => indicator (H = G)) := by
  have h := poissonGraphMean_relabel e t (fun H => indicator (H = relabel e G))
  simpa only [(relabel_injective e).eq_iff] using h.symm

theorem induced_left_eq {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (G : MGraph (A ⊕ B)) :
    inducedGraph G (leftBlock A B) = relabel (leftEquiv A B) (restrictLeft G) := by
  funext e
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨a, rfl⟩ := (leftEquiv A B).surjective x
    obtain ⟨b, rfl⟩ := (leftEquiv A B).surjective y
    change G s(Sum.inl a, Sum.inl b) =
      mapGraph (leftEquiv A B) (restrictLeft G) (Sym2.map (leftEquiv A B) s(a,b))
    rw [ThLean.W.S391.mapGraph_embedding_apply _ (leftEquiv A B).injective]
    rfl

theorem induced_right_eq {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (G : MGraph (A ⊕ B)) :
    inducedGraph G (rightBlock A B) = relabel (rightEquiv A B) (restrictRight G) := by
  funext e
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨a, rfl⟩ := (rightEquiv A B).surjective x
    obtain ⟨b, rfl⟩ := (rightEquiv A B).surjective y
    change G s(Sum.inr a, Sum.inr b) =
      mapGraph (rightEquiv A B) (restrictRight G) (Sym2.map (rightEquiv A B) s(a,b))
    rw [ThLean.W.S391.mapGraph_embedding_apply _ (rightEquiv A B).injective]
    rfl

theorem splitNeighbors_event {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (w : List (Pair (A ⊕ B))) (xs : A → List B) :
    (∀ a : {v : A ⊕ B // v ∈ leftBlock A B},
      ThLean.BP.S3.neighborList a.val (rightBlock A B) w =
        (xs ((leftEquiv A B).symm a)).map Sum.inr) ↔ splitNeighbors w = xs := by
  constructor
  · intro hs
    funext a
    have hh := congrArg (List.filterMap getRight) (hs (leftEquiv A B a))
    simpa [splitNeighbors, leftEquiv, List.filterMap_map, getRight, Function.comp_def] using hh
  · intro hs a
    obtain ⟨a, rfl⟩ := (leftEquiv A B).surjective a
    change ThLean.BP.S3.neighborList (Sum.inl a) (rightBlock A B) w = _
    rw [Equiv.symm_apply_apply]
    exact (map_splitNeighbors w a).symm.trans (congrArg (List.map Sum.inr) (congrFun hs a))

theorem split_event {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (w : List (Pair (A ⊕ B))) (GA : MGraph A) (GB : MGraph B) (xs : A → List B) :
    (inducedGraph (listGraph w) (rightBlock A B) = relabel (rightEquiv A B) GB ∧
      inducedGraph (listGraph w) (leftBlock A B) = relabel (leftEquiv A B) GA ∧
      ∀ a : {v : A ⊕ B // v ∈ leftBlock A B},
        ThLean.BP.S3.neighborList a.val (rightBlock A B) w =
          (xs ((leftEquiv A B).symm a)).map Sum.inr) ↔
      (restrictLeft (listGraph w) = GA ∧ restrictRight (listGraph w) = GB ∧
        splitNeighbors w = xs) := by
  rw [induced_left_eq, induced_right_eq, (relabel_injective (leftEquiv A B)).eq_iff,
    (relabel_injective (rightEquiv A B)).eq_iff, splitNeighbors_event]
  tauto

theorem listMass_map_inr {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (z : ℝ) (xs : List B) :
    poissonListMass z
      (fun v : A ⊕ B => if v ∈ rightBlock A B then 1 / ((rightBlock A B).card : ℝ) else 0)
      (xs.map Sum.inr) =
      poissonListMass z (fun _ : B => 1 / (Fintype.card B : ℝ)) xs := by
  simp [poissonListMass, List.map_map, Function.comp_def]

theorem split_atom {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (h37 : S3_37aStatement.{max u v}) (hTotal : 3 ≤ Fintype.card (A ⊕ B))
    (hB : 2 ≤ Fintype.card B) (t : ℝ) (ht : 0 ≤ t)
    (GA : MGraph A) (GB : MGraph B) (xs : A → List B) :
    poissonWordProb t (fun w => restrictLeft (listGraph w) = GA ∧
      restrictRight (listGraph w) = GB ∧ splitNeighbors w = xs) =
    poissonGraphMean
      (t * ((Fintype.card A).choose 2 : ℝ) / ((Fintype.card (A ⊕ B)).choose 2 : ℝ))
      (fun G => indicator (G = GA)) *
    poissonGraphMean
      (t * ((Fintype.card B).choose 2 : ℝ) / ((Fintype.card (A ⊕ B)).choose 2 : ℝ))
      (fun G => indicator (G = GB)) *
    ∏ a : A, poissonListMass
      (t * Fintype.card B / ((Fintype.card (A ⊕ B)).choose 2 : ℝ))
      (fun _ : B => 1 / (Fintype.card B : ℝ)) (xs a) := by
  letI : DecidableEq (A ⊕ B) := Classical.decEq (A ⊕ B)
  have hcard := (ThLean.W.S302.S3_03aStatement_holds (A ⊕ B) (by omega)).1
  have hRight : Finset.univ \ leftBlock A B = rightBlock A B := by
    ext x
    simp [rightBlock]
  have hs := h37 (A ⊕ B) (leftBlock A B) hTotal
  dsimp only at hs
  rw [hRight] at hs
  specialize hs (by simpa only [rightBlock_card] using hB)
    t ht (relabel (rightEquiv A B) GB) (relabel (leftEquiv A B) GA)
    (fun a => (xs ((leftEquiv A B).symm a)).map Sum.inr)
  change poissonWordProb t (fun w =>
    inducedGraph (listGraph w) (rightBlock A B) = relabel (rightEquiv A B) GB ∧
    inducedGraph (listGraph w) (leftBlock A B) = relabel (leftEquiv A B) GA ∧
    ∀ a, ThLean.BP.S3.neighborList a.val (rightBlock A B) w =
      (xs ((leftEquiv A B).symm a)).map Sum.inr) = _ at hs
  have he : (fun w => inducedGraph (listGraph w) (rightBlock A B) = relabel (rightEquiv A B) GB ∧
    inducedGraph (listGraph w) (leftBlock A B) = relabel (leftEquiv A B) GA ∧
    ∀ a, ThLean.BP.S3.neighborList a.val (rightBlock A B) w =
      (xs ((leftEquiv A B).symm a)).map Sum.inr) =
      (fun w => restrictLeft (listGraph w) = GA ∧ restrictRight (listGraph w) = GB ∧
        splitNeighbors w = xs) := by
    funext w
    exact propext (split_event w GA GB xs)
  rw [he] at hs
  simp only [rightBlock_card, leftBlock_card, hcard, poissonGraphProb_relabel] at hs
  have hp (z : ℝ) :
      (∏ a : {v : A ⊕ B // v ∈ leftBlock A B}, poissonListMass z
        (fun v : A ⊕ B => if v ∈ rightBlock A B then 1 / (Fintype.card B : ℝ) else 0)
        ((xs ((leftEquiv A B).symm a)).map Sum.inr)) =
        ∏ a : A, poissonListMass z (fun _ : B => 1 / (Fintype.card B : ℝ)) (xs a) := by
    rw [← (leftEquiv A B).prod_comp]
    simp [poissonListMass, List.map_map, Function.comp_def]
  rw [hp] at hs
  exact hs.trans (by ring)

end ThLean.W.S390S

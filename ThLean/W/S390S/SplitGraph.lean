import ThLean.W.S391.SplitRoot

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S390S
open ThresholdFoundations ThLean.BP.S3
universe u v

def leftBlock (A : Type u) (B : Type v) [Fintype A] [Fintype B] : Finset (A ⊕ B) :=
  Finset.univ.filter (fun x => x.isLeft = true)

def rightBlock (A : Type u) (B : Type v) [Fintype A] [Fintype B] : Finset (A ⊕ B) :=
  Finset.univ \ leftBlock A B

@[simp] theorem mem_leftBlock {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (x : A ⊕ B) : x ∈ leftBlock A B ↔ x.isLeft := by
  simp [leftBlock]

@[simp] theorem mem_rightBlock {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (x : A ⊕ B) : x ∈ rightBlock A B ↔ x.isRight := by
  cases x <;> simp [rightBlock, leftBlock]

def leftEquiv (A : Type u) (B : Type v) [Fintype A] [Fintype B] :
    A ≃ {x : A ⊕ B // x ∈ leftBlock A B} where
  toFun a := ⟨Sum.inl a, by simp⟩
  invFun x := match x with
    | ⟨Sum.inl a, _⟩ => a
    | ⟨Sum.inr b, h⟩ => False.elim (by simpa using h)
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨a | b, h⟩
    · rfl
    · exact False.elim (by simpa only [mem_leftBlock, Sum.isLeft_inr, Bool.false_eq_true] using h)

def rightEquiv (A : Type u) (B : Type v) [Fintype A] [Fintype B] :
    B ≃ {x : A ⊕ B // x ∈ rightBlock A B} where
  toFun b := ⟨Sum.inr b, by simp⟩
  invFun x := match x with
    | ⟨Sum.inl a, h⟩ => False.elim (by simpa using h)
    | ⟨Sum.inr b, _⟩ => b
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨a | b, h⟩
    · exact False.elim (by simpa only [mem_rightBlock, Sum.isRight_inl, Bool.false_eq_true] using h)
    · rfl

@[simp] theorem leftBlock_card (A : Type u) (B : Type v) [Fintype A] [Fintype B] :
    (leftBlock A B).card = Fintype.card A := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (leftEquiv A B)).symm

@[simp] theorem rightBlock_card (A : Type u) (B : Type v) [Fintype A] [Fintype B] :
    (rightBlock A B).card = Fintype.card B := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (rightEquiv A B)).symm

def restrictLeft {A : Type u} {B : Type v} (G : MGraph (A ⊕ B)) : MGraph A :=
  fun e => G (Sym2.map Sum.inl e)

def restrictRight {A : Type u} {B : Type v} (G : MGraph (A ⊕ B)) : MGraph B :=
  fun e => G (Sym2.map Sum.inr e)

def getRight {A : Type u} {B : Type v} : A ⊕ B → Option B
  | .inl _ => none
  | .inr b => some b

def splitNeighbors {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (w : List (Pair (A ⊕ B))) (a : A) : List B :=
  (ThLean.BP.S3.neighborList (Sum.inl a) (rightBlock A B) w).filterMap getRight

theorem neighborList_mem {V : Type*} [Fintype V] (a : V) (S : Finset V)
    (w : List (Pair V)) {b : V} (hb : b ∈ ThLean.BP.S3.neighborList a S w) : b ∈ S := by
  obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hb
  change (if h : ∃ v ∈ S, p.val = s(a,v) then some (Classical.choose h) else none) = some b at hp
  split_ifs at hp with h
  · have heq := Option.some.inj hp
    exact heq ▸ (Classical.choose_spec h).1

theorem map_splitNeighbors {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (w : List (Pair (A ⊕ B))) (a : A) :
    (splitNeighbors w a).map Sum.inr =
      ThLean.BP.S3.neighborList (Sum.inl a) (rightBlock A B) w := by
  let ys := ThLean.BP.S3.neighborList (Sum.inl a) (rightBlock A B) w
  have hs : ∀ x ∈ ys, x.isRight := by
    intro x hx
    exact (mem_rightBlock x).mp (neighborList_mem _ _ _ hx)
  change (ys.filterMap getRight).map Sum.inr = ys
  have hm : ∀ zs : List (A ⊕ B), (∀ x ∈ zs, x.isRight) →
      (zs.filterMap getRight).map Sum.inr = zs := by
    intro zs
    induction zs with
    | nil => intro _; rfl
    | cons x xs ih =>
      intro hx
      cases x with
      | inl a => exact False.elim (by simpa using hx _ List.mem_cons_self)
      | inr b =>
        simpa only [List.filterMap_cons, getRight, List.map_cons] using
          congrArg (List.cons (Sum.inr b)) (ih (fun x hx' => hx x (List.mem_cons_of_mem _ hx')))
  exact hm ys hs

theorem neighborList_count {V : Type*} [Fintype V] [BEq V] [LawfulBEq V] (a : V) (S : Finset V)
    (w : List (Pair V)) (b : V) (hb : b ∈ S) :
    (ThLean.BP.S3.neighborList a S w).count b = listGraph w s(a,b) := by
  induction w with
  | nil => simp [ThLean.BP.S3.neighborList, listGraph]
  | cons p w ih =>
    by_cases hp : ∃ v ∈ S, p.val = s(a,v)
    · have hc := (Classical.choose_spec hp).2
      have he : (p.val = s(a,b)) ↔ Classical.choose hp = b := by
        constructor
        · intro h
          exact Sym2.congr_right.mp (hc.symm.trans h)
        · intro h
          exact hc.trans (congrArg (fun c => s(a,c)) h)
      simp only [ThLean.BP.S3.neighborList, List.filterMap_cons, dif_pos hp]
      change (Classical.choose hp :: ThLean.BP.S3.neighborList a S w).count b = _
      rw [List.count_cons, ih]
      change _ = ((p :: w).filter (fun q => decide (q.val = s(a,b)))).length
      by_cases h : Classical.choose hp = b
      · have hp' := he.mpr h
        simp only [h, beq_self_eq_true, ite_true]
        conv_rhs => simp only [List.filter_cons, hp', decide_true, ite_true,
          List.length_cons]
        rfl
      · have hp' : p.val ≠ s(a,b) := fun h' => h (he.mp h')
        simp [h, hp', List.filter_cons, listGraph, Ne.symm h]
    · have hn : p.val ≠ s(a,b) := fun h => hp ⟨b, hb, h⟩
      simpa [ThLean.BP.S3.neighborList, hp, listGraph, hn] using ih

theorem splitNeighbors_count {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (w : List (Pair (A ⊕ B))) (a : A) (b : B) :
    (splitNeighbors w a).count b = listGraph w s(Sum.inl a,Sum.inr b) := by
  have hm := map_splitNeighbors w a
  have hc := List.count_map_of_injective (splitNeighbors w a)
    (Sum.inr : B → A ⊕ B) Sum.inr_injective b
  rw [hm] at hc
  rw [← hc]
  exact neighborList_count (Sum.inl a) (rightBlock A B) w (Sum.inr b) (by simp)

theorem mapGraph_inl_mk {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (G : MGraph A) (x y : A ⊕ B) :
    mapGraph Sum.inl G s(x,y) = match x, y with
      | .inl a, .inl b => G s(a,b)
      | _, _ => 0 := by
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      exact ThLean.W.S391.mapGraph_embedding_apply
        (Sum.inl : A → A ⊕ B) Sum.inl_injective G s(a,b)
    | inr b =>
      apply Finset.sum_eq_zero
      intro e he
      induction e using Sym2.ind with
      | h c d => simp
  | inr a =>
    apply Finset.sum_eq_zero
    intro e he
    induction e using Sym2.ind with
    | h c d => cases y <;> simp

theorem mapGraph_inr_mk {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (G : MGraph B) (x y : A ⊕ B) :
    mapGraph Sum.inr G s(x,y) = match x, y with
      | .inr a, .inr b => G s(a,b)
      | _, _ => 0 := by
  cases x with
  | inr a =>
    cases y with
    | inr b =>
      exact ThLean.W.S391.mapGraph_embedding_apply
        (Sum.inr : B → A ⊕ B) Sum.inr_injective G s(a,b)
    | inl b =>
      apply Finset.sum_eq_zero
      intro e he
      induction e using Sym2.ind with
      | h c d => simp
  | inl a =>
    apply Finset.sum_eq_zero
    intro e he
    induction e using Sym2.ind with
    | h c d => cases y <;> simp

theorem splitUnionGraph_mk {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (GA : MGraph A) (GB : MGraph B) (xs : A → List B) (x y : A ⊕ B) :
    splitUnionGraph GA GB xs s(x,y) = match x, y with
      | .inl a, .inl b => GA s(a,b)
      | .inr a, .inr b => GB s(a,b)
      | .inl a, .inr b => (xs a).count b
      | .inr b, .inl a => (xs a).count b := by
  have hll (a : A) (b c : A) (ys : List B) :
      (ys.map (fun d => s(Sum.inl a, Sum.inr d))).count s(Sum.inl b,Sum.inl c) = 0 := by
    induction ys with
    | nil => simp
    | cons d ys ih => simp [List.count_cons, Sym2.eq_iff, ih]
  have hrr (a : A) (b c : B) (ys : List B) :
      (ys.map (fun d => s(Sum.inl a, Sum.inr d))).count s(Sum.inr b,Sum.inr c) = 0 := by
    induction ys with
    | nil => simp
    | cons d ys ih => simp [List.count_cons, Sym2.eq_iff, ih]
  have hlr (a c : A) (b : B) (ys : List B) :
      (ys.map (fun d => s(Sum.inl a, Sum.inr d))).count s(Sum.inl c,Sum.inr b) =
        if a = c then ys.count b else 0 := by
    induction ys with
    | nil => simp
    | cons d ys ih =>
      by_cases ha : a = c <;> by_cases hd : d = b <;>
        simp_all [List.count_cons, Sym2.eq_iff]
  cases x <;> cases y <;>
    simp [splitUnionGraph, mapGraph_inl_mk, mapGraph_inr_mk, hll, hrr, hlr,
      Sym2.eq_swap (a := Sum.inr _) (b := Sum.inl _)]

theorem splitUnionGraph_reconstruct {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (w : List (Pair (A ⊕ B))) :
    splitUnionGraph (restrictLeft (listGraph w)) (restrictRight (listGraph w))
      (splitNeighbors w) = listGraph w := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    cases x <;> cases y <;>
      simp [splitUnionGraph_mk, restrictLeft, restrictRight, splitNeighbors_count,
        Sym2.eq_swap]

end ThLean.W.S390S

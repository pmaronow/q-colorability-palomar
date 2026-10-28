import ThLean.W.S369S.ListGraph

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S369S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V]

def thetaLabels (a b : V) (x y z : List V) : List V := [a,b] ++ x ++ y ++ z

def thetaLists (a b : V) (x y z : List V) : MGraph V :=
  edgesGraph (consecutiveEdges ([a] ++ x ++ [b]) ++
    consecutiveEdges ([a] ++ y ++ [b]) ++ consecutiveEdges ([a] ++ z ++ [b]))

theorem support_thetaLists (a b : V) (x y z : List V) :
    vertexSupport (thetaLists a b x y z) = (thetaLabels a b x y z).toFinset := by
  unfold thetaLists
  rw [support_append, support_append]
  rw [support_consecutiveEdges _ (by simp),
    support_consecutiveEdges _ (by simp),
    support_consecutiveEdges _ (by simp)]
  ext t
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, thetaLabels]
  tauto

def tuplePath (es : List (Sym2 V)) {n : ℕ} (f : Fin (n+1) → V)
    (hf : Function.Injective f) (ι : Fin n ↪ Fin es.length)
    (he : ∀ i, es.get (ι i) = s(f i.castSucc, f i.succ)) :
    OccurrencePath (edgesGraph es) where
  length := n
  vertex := f
  edge := fun i => listOccEquiv es (ι i)
  vertex_injective := hf
  edge_injective := (listOccEquiv es).injective.comp ι.injective
  joins := fun i => (listOccEquiv_pair es (ι i)).trans (he i)

def branch (a b : V) (xs : List V) : Fin (xs.length+2) → V :=
  fun i => ([a] ++ xs ++ [b])[i.val]'(by simp; omega)

@[simp] theorem branch_ofFn (a b : V) (xs : List V) :
    List.ofFn (branch a b xs) = [a] ++ xs ++ [b] := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, branch]

theorem branch_injective (a b : V) (xs : List V)
    (hn : ([a] ++ xs ++ [b]).Nodup) : Function.Injective (branch a b xs) := by
  intro i j hij
  apply Fin.ext
  exact List.Nodup.getElem_inj_iff hn |>.mp hij

theorem branch_edge_get (a b : V) (xs : List V) (i : Fin (xs.length+1)) :
    (consecutiveEdges ([a] ++ xs ++ [b]))[i.val]'(by
      rw [ThLean.W.S369.consecutiveEdges_length]; simp; omega) =
      s(branch a b xs i.castSucc, branch a b xs i.succ) := by
  exact consecutiveEdges_get _ i.val (by simp; omega)

theorem mem_branch (a b : V) (xs : List V) (t : V) :
    (∃ i, branch a b xs i = t) ↔ t = a ∨ t ∈ xs ∨ t = b := by
  rw [← List.mem_ofFn, branch_ofFn]
  simp

@[simp] theorem branch_start (a b : V) (xs : List V) : branch a b xs 0 = a := by
  simp [branch]

@[simp] theorem branch_end (a b : V) (xs : List V) :
    branch a b xs (Fin.last (xs.length+1)) = b := by
  simp only [branch, Fin.val_last]
  simp only [List.getElem_append, List.length_append, List.length_singleton]
  simp [Nat.add_comm]

theorem thetaLabels_branches (a b : V) (x y z : List V)
    (hn : (thetaLabels a b x y z).Nodup) :
    ([a] ++ x ++ [b]).Nodup ∧ ([a] ++ y ++ [b]).Nodup ∧
    ([a] ++ z ++ [b]).Nodup := by
  simp only [thetaLabels, List.nodup_append, List.nodup_cons, List.nodup_nil,
    List.mem_cons, List.not_mem_nil, or_false, and_true] at hn
  simp only [List.nodup_append, List.nodup_cons, List.nodup_nil,
    List.mem_cons, List.not_mem_nil, or_false, and_true]
  aesop

theorem thetaLabels_separate (a b : V) (x y z : List V)
    (hn : (thetaLabels a b x y z).Nodup) :
    a ≠ b ∧ (∀ t ∈ x, t ∉ y) ∧ (∀ t ∈ x, t ∉ z) ∧ (∀ t ∈ y, t ∉ z) := by
  have hz := List.nodup_append.mp hn
  have hy := List.nodup_append.mp hz.1
  have hx := List.nodup_append.mp hy.1
  refine ⟨by simpa using hx.1, ?_, ?_, ?_⟩
  · intro t ht hu
    exact hy.2.2 t (List.mem_append_right _ ht) t hu rfl
  · intro t ht hu
    exact hz.2.2 t (List.mem_append_left _ (List.mem_append_right _ ht)) t hu rfl
  · intro t ht hu
    exact hz.2.2 t (List.mem_append_right _ ht) t hu rfl

def segmentIndex (offset n total : ℕ) (h : offset+n ≤ total) : Fin n ↪ Fin total where
  toFun i := ⟨offset+i.val, by omega⟩
  inj' := by intro i j hij; apply Fin.ext; have := congrArg Fin.val hij; dsimp at this; omega

theorem thetaLists_exact (a b : V) (x y z : List V)
    (hn : (thetaLabels a b x y z).Nodup) : ExactTheta (thetaLists a b x y z) := by
  obtain ⟨hx, hy, hz⟩ := thetaLabels_branches a b x y z hn
  obtain ⟨hab, hxy, hxz, hyz⟩ := thetaLabels_separate a b x y z hn
  let ex := consecutiveEdges ([a] ++ x ++ [b])
  let ey := consecutiveEdges ([a] ++ y ++ [b])
  let ez := consecutiveEdges ([a] ++ z ++ [b])
  let es := ex ++ ey ++ ez
  change ExactTheta (edgesGraph es)
  unfold ExactTheta
  have lx : ex.length = x.length+1 := by
    simp [ex, ThLean.W.S369.consecutiveEdges_length]
  have ly : ey.length = y.length+1 := by
    simp [ey, ThLean.W.S369.consecutiveEdges_length]
  have lz : ez.length = z.length+1 := by
    simp [ez, ThLean.W.S369.consecutiveEdges_length]
  have les : es.length = x.length+1+(y.length+1)+(z.length+1) := by
    simp only [es, List.length_append, lx, ly, lz]
  let ix := segmentIndex 0 (x.length+1) es.length (by omega)
  let iy := segmentIndex (x.length+1) (y.length+1) es.length (by omega)
  let iz := segmentIndex (x.length+1+(y.length+1)) (z.length+1) es.length (by omega)
  have jx (i : Fin (x.length+1)) :
      es.get (ix i) = s(branch a b x i.castSucc, branch a b x i.succ) := by
    change (ex ++ ey ++ ez)[0+i.val]'(by simp only [List.length_append]; omega) = _
    simp only [Nat.zero_add]
    rw [List.getElem_append_left (by simp only [List.length_append]; omega),
      List.getElem_append_left (by omega)]
    exact branch_edge_get a b x i
  have jy (i : Fin (y.length+1)) :
      es.get (iy i) = s(branch a b y i.castSucc, branch a b y i.succ) := by
    change (ex ++ ey ++ ez)[x.length+1+i.val]'(by simp only [List.length_append]; omega) = _
    rw [List.getElem_append_left (by simp only [List.length_append]; omega),
      List.getElem_append_right (by omega)]
    simp only [lx, Nat.add_sub_cancel_left]
    exact branch_edge_get a b y i
  have jz (i : Fin (z.length+1)) :
      es.get (iz i) = s(branch a b z i.castSucc, branch a b z i.succ) := by
    change (ex ++ ey ++ ez)[x.length+1+(y.length+1)+i.val]'(by simp only [List.length_append]; omega) = _
    rw [List.getElem_append_right (by simp only [List.length_append]; omega)]
    simp only [List.length_append, lx, ly, Nat.add_sub_cancel_left]
    exact branch_edge_get a b z i
  let px := tuplePath es (branch a b x) (branch_injective a b x hx) ix jx
  let py := tuplePath es (branch a b y) (branch_injective a b y hy) iy jy
  let pz := tuplePath es (branch a b z) (branch_injective a b z hz) iz jz
  have dx : Disjoint (pathOccurrences px) (pathOccurrences py) := by
    apply Finset.disjoint_left.mpr
    intro o ho hp
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp
    have hh := (listOccEquiv es).injective (hi.trans hj.symm)
    have hh' := congrArg Fin.val hh
    change 0+i.val = x.length+1+j.val at hh'
    have hi : i.val < x.length+1 := i.isLt
    omega
  have dz : Disjoint (pathOccurrences px) (pathOccurrences pz) := by
    apply Finset.disjoint_left.mpr
    intro o ho hp
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp
    have hh := (listOccEquiv es).injective (hi.trans hj.symm)
    have hh' := congrArg Fin.val hh
    change 0+i.val = x.length+1+(y.length+1)+j.val at hh'
    have hi : i.val < x.length+1 := i.isLt
    omega
  have dy : Disjoint (pathOccurrences py) (pathOccurrences pz) := by
    apply Finset.disjoint_left.mpr
    intro o ho hp
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp
    have hh := (listOccEquiv es).injective (hi.trans hj.symm)
    have hh' := congrArg Fin.val hh
    change x.length+1+i.val = x.length+1+(y.length+1)+j.val at hh'
    have hi : i.val < y.length+1 := i.isLt
    omega
  have vx : pathVertices px ∩ pathVertices py ⊆ {a,b} := by
    intro t ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ht).1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ht).2
    have h1 := (mem_branch a b x t).mp ⟨i, hi⟩
    have h2 := (mem_branch a b y t).mp ⟨j, hj⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    aesop
  have vz : pathVertices px ∩ pathVertices pz ⊆ {a,b} := by
    intro t ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ht).1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ht).2
    have h1 := (mem_branch a b x t).mp ⟨i, hi⟩
    have h2 := (mem_branch a b z t).mp ⟨j, hj⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    aesop
  have vy : pathVertices py ∩ pathVertices pz ⊆ {a,b} := by
    intro t ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ht).1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ht).2
    have h1 := (mem_branch a b y t).mp ⟨i, hi⟩
    have h2 := (mem_branch a b z t).mp ⟨j, hj⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    aesop
  refine ⟨a, b, hab, px, py, pz, ?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.mem_singleton] at hp
    simp only [List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp [px, py, pz, tuplePath, PathFrom, branch_start, branch_end] <;>
      exact branch_end _ _ _
  · simpa only [List.pairwise_cons, List.pairwise_singleton, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, List.Pairwise.nil, forall_eq_or_imp,
      forall_eq, IsEmpty.forall_iff, imp_false, implies_true, and_true] using
      And.intro (And.intro (And.intro dx vx) (And.intro dz vz)) (And.intro dy vy)
  · apply Finset.eq_univ_of_forall
    intro o
    obtain ⟨i, rfl⟩ := (listOccEquiv es).surjective o
    simp only [Finset.mem_union]
    by_cases hix : i.val < x.length+1
    · left; left
      apply Finset.mem_image.mpr
      refine ⟨⟨i.val, hix⟩, Finset.mem_univ _, ?_⟩
      apply congrArg (listOccEquiv es)
      apply Fin.ext
      simp [ix, segmentIndex]
    · by_cases hiy : i.val < x.length+1+(y.length+1)
      · left; right
        apply Finset.mem_image.mpr
        refine ⟨(⟨i.val-(x.length+1), by omega⟩ : Fin (y.length+1)), Finset.mem_univ _, ?_⟩
        apply congrArg (listOccEquiv es)
        apply Fin.ext
        dsimp [iy, segmentIndex]
        omega
      · right
        apply Finset.mem_image.mpr
        refine ⟨(⟨i.val-(x.length+1+(y.length+1)), by omega⟩ : Fin (z.length+1)), Finset.mem_univ _, ?_⟩
        apply congrArg (listOccEquiv es)
        apply Fin.ext
        dsimp [iz, segmentIndex]
        omega

end ThLean.W.S369S

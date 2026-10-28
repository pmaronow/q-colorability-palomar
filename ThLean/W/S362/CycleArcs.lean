import ThLean.W.S362.CycleIndex

noncomputable section
open scoped BigOperators
namespace ThLean.W.S362
open ThresholdFoundations
universe u
variable {V : Type u} [Fintype V]
attribute [local instance] Classical.propDecidable

def arcForward {G : MGraph V} (c : OccurrenceCycle G) (k : Fin c.length) :
    OccurrencePath G :=
  { length := k.val
    vertex := fun i => c.vertex ⟨i.val, by omega⟩
    edge := fun i => c.edge ⟨i.val, by omega⟩
    vertex_injective := by
      intro i j hij
      change c.vertex ⟨i.val, by omega⟩ = c.vertex ⟨j.val, by omega⟩ at hij
      have hidx := c.vertex_injective hij
      have hval : i.val = j.val := congrArg (fun x : Fin c.length => x.val) hidx
      exact Fin.ext hval
    edge_injective := by
      intro i j hij
      change c.edge ⟨i.val, by omega⟩ = c.edge ⟨j.val, by omega⟩ at hij
      have hidx := c.edge_injective hij
      have hval : i.val = j.val := congrArg (fun x : Fin c.length => x.val) hidx
      exact Fin.ext hval
    joins := by
      intro i
      have hi : i.val + 1 < c.length := by omega
      simpa [Nat.mod_eq_of_lt hi] using c.joins ⟨i.val, by omega⟩ }

def arcWrap {G : MGraph V} (c : OccurrenceCycle G) (k : Fin c.length)
    (hk : 0 < k.val) :
    OccurrencePath G :=
  { length := c.length - k.val
    vertex := fun i => c.vertex ⟨(k.val+i.val)%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩
    edge := fun i => c.edge ⟨k.val+i.val, by omega⟩
    vertex_injective := by
      intro i j hij
      have hi : i.val ≤ c.length-k.val := Nat.le_of_lt_succ i.isLt
      have hj : j.val ≤ c.length-k.val := Nat.le_of_lt_succ j.isLt
      have hi' : i.val < c.length := by omega
      have hj' : j.val < c.length := by omega
      change c.vertex ⟨(k.val+i.val)%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩ =
        c.vertex ⟨(k.val+j.val)%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩ at hij
      have heq : (k.val+i.val)%c.length = (k.val+j.val)%c.length :=
        congrArg Fin.val (c.vertex_injective hij)
      have hmod : k.val+i.val ≡ k.val+j.val [MOD c.length] := heq
      have hcancel : i.val ≡ j.val [MOD c.length] :=
        Nat.ModEq.add_left_cancel (Nat.ModEq.refl k.val) hmod
      change i.val % c.length = j.val % c.length at hcancel
      rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hcancel
      exact Fin.ext hcancel
    edge_injective := by
      intro i j hij
      change c.edge ⟨k.val+i.val, by omega⟩ = c.edge ⟨k.val+j.val, by omega⟩ at hij
      have hidx := c.edge_injective hij
      have hval : k.val+i.val = k.val+j.val :=
        congrArg (fun x : Fin c.length => x.val) hidx
      exact Fin.ext (by omega)
    joins := by
      intro i
      let t : Fin c.length := ⟨k.val+i.val, by omega⟩
      have hstart : (⟨(k.val+i.val)%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩ : Fin c.length) = t := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega)
      have hnext :
          (⟨(k.val+(i.val+1))%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩ : Fin c.length) =
            ⟨(t.val+1)%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩ := by
        apply Fin.ext
        exact (congrArg (fun x => x % c.length) (Nat.add_assoc k.val i.val 1)).symm
      rw [hstart, hnext]
      exact c.joins t }

theorem arcWrap_from {G : MGraph V} (c : OccurrenceCycle G) (k : Fin c.length)
    (hk : 0 < k.val) : PathFrom (arcWrap c k hk) (c.vertex k)
      (c.vertex (zeroFin c.length (cycleLen_pos c))) := by
  constructor
  · apply congrArg c.vertex
    apply Fin.ext
    exact Nat.mod_eq_of_lt k.isLt
  · apply congrArg c.vertex
    apply Fin.ext
    change (k.val+(c.length-k.val))%c.length = 0
    rw [Nat.add_sub_of_le (le_of_lt k.isLt), Nat.mod_self]

theorem arcForward_from {G : MGraph V} (c : OccurrenceCycle G) (k : Fin c.length) :
    PathFrom (arcForward c k) (c.vertex (zeroFin c.length (cycleLen_pos c)))
      (c.vertex k) := by
  constructor
  · apply congrArg c.vertex
    apply Fin.ext
    rfl
  · apply congrArg c.vertex
    apply Fin.ext
    rfl

theorem arc_occ_disjoint {G : MGraph V} (c : OccurrenceCycle G)
    (k : Fin c.length) (hk : 0 < k.val) :
    Disjoint (pathOccurrences (arcForward c k)) (pathOccurrences (arcWrap c k hk)) := by
  classical
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rcases Finset.mem_image.mp he₁ with ⟨i, -, hi⟩
  rcases Finset.mem_image.mp he₂ with ⟨j, -, hj⟩
  have hi_bound : i.val < k.val := by simpa [arcForward] using i.isLt
  have hj_bound : j.val < c.length-k.val := by simpa [arcWrap] using j.isLt
  have hedge : c.edge ⟨i.val, by omega⟩ = c.edge ⟨k.val+j.val, by omega⟩ := by
    have h₁ : c.edge ⟨i.val, by omega⟩ = e := by simpa [arcForward] using hi
    have h₂ : c.edge ⟨k.val+j.val, by omega⟩ = e := by simpa [arcWrap] using hj
    exact h₁.trans h₂.symm
  have hidx := c.edge_injective hedge
  have hv : i.val = k.val+j.val :=
    congrArg (fun x : Fin c.length => x.val) hidx
  omega

theorem arc_occ_union {G : MGraph V} (c : OccurrenceCycle G)
    (k : Fin c.length) (hk : 0 < k.val) :
    pathOccurrences (arcForward c k) ∪ pathOccurrences (arcWrap c k hk) = cycleOccurrences c := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.mp he with hp | hq
    · rcases Finset.mem_image.mp hp with ⟨i, -, hi⟩
      have hi_bound : i.val < k.val := by simpa [arcForward] using i.isLt
      refine Finset.mem_image.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, ?_⟩
      simpa [arcForward] using hi
    · rcases Finset.mem_image.mp hq with ⟨j, -, hj⟩
      have hj_bound : j.val < c.length-k.val := by simpa [arcWrap] using j.isLt
      refine Finset.mem_image.mpr ⟨⟨k.val+j.val, by omega⟩, Finset.mem_univ _, ?_⟩
      simpa [arcWrap] using hj
  · intro he
    rcases Finset.mem_image.mp he with ⟨i, -, hi⟩
    by_cases hik : i.val < k.val
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨⟨i.val, hik⟩, Finset.mem_univ _, ?_⟩
      simpa [arcForward] using hi
    · have hki : k.val ≤ i.val := le_of_not_gt hik
      have hj : i.val-k.val < c.length-k.val := by omega
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨⟨i.val-k.val, hj⟩, Finset.mem_univ _, ?_⟩
      have heq : k.val + (i.val-k.val) = i.val := by omega
      simpa [arcWrap, heq] using hi

theorem arc_vertex_inter {G : MGraph V} (c : OccurrenceCycle G)
    (k : Fin c.length) (hk : 0 < k.val) :
    pathVertices (arcForward c k) ∩ pathVertices (arcWrap c k hk) =
      {c.vertex (zeroFin c.length (cycleLen_pos c)), c.vertex k} := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hp, hq⟩
    rcases Finset.mem_image.mp hp with ⟨i, -, hi⟩
    rcases Finset.mem_image.mp hq with ⟨j, -, hj⟩
    have ibound : i.val ≤ k.val := by
      simpa [arcForward] using Nat.le_of_lt_succ i.isLt
    have jbound : j.val ≤ c.length-k.val := by
      simpa [arcWrap] using Nat.le_of_lt_succ j.isLt
    have hi' : c.vertex ⟨i.val, by omega⟩ = x := by simpa [arcForward] using hi
    have hj' : c.vertex ⟨(k.val+j.val)%c.length,
        Nat.mod_lt _ (cycleLen_pos c)⟩ = x := by simpa [arcWrap] using hj
    have hidx : (⟨i.val, by omega⟩ : Fin c.length) =
        ⟨(k.val+j.val)%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩ :=
      c.vertex_injective (hi'.trans hj'.symm)
    have hval : i.val = (k.val+j.val)%c.length :=
      congrArg (fun x : Fin c.length => x.val) hidx
    by_cases hjlast : j.val = c.length-k.val
    · have hzero : (k.val+j.val)%c.length = 0 := by
        rw [hjlast, Nat.add_sub_of_le (le_of_lt k.isLt), Nat.mod_self]
      have hi0 : i.val = 0 := by omega
      have hfin : (⟨i.val, by omega⟩ : Fin c.length) =
          zeroFin c.length (cycleLen_pos c) := Fin.ext hi0
      rw [hfin] at hi'
      simp [hi']
    · have hjlt : j.val < c.length-k.val := by omega
      have hsumlt : k.val+j.val < c.length := by omega
      have hij : i.val = k.val+j.val := by
        rw [Nat.mod_eq_of_lt hsumlt] at hval
        exact hval
      have hj0 : j.val = 0 := by omega
      have hik : i.val = k.val := by omega
      have hfi : (⟨i.val, by omega⟩ : Fin c.length) = k := Fin.ext hik
      rw [hfi] at hi'
      simp [hi']
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · subst x
      apply Finset.mem_inter.mpr
      constructor
      · change c.vertex (zeroFin c.length (cycleLen_pos c)) ∈
          Finset.univ.image (fun i : Fin (k.val+1) => c.vertex ⟨i.val, by omega⟩)
        refine Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
        apply congrArg c.vertex
        apply Fin.ext
        rfl
      · change c.vertex (zeroFin c.length (cycleLen_pos c)) ∈
          Finset.univ.image (fun j : Fin (c.length-k.val+1) =>
            c.vertex ⟨(k.val+j.val)%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩)
        refine Finset.mem_image.mpr ⟨⟨c.length-k.val, by omega⟩, Finset.mem_univ _, ?_⟩
        apply congrArg c.vertex
        apply Fin.ext
        change (k.val+(c.length-k.val))%c.length = 0
        rw [Nat.add_sub_of_le (le_of_lt k.isLt), Nat.mod_self]
    · subst x
      apply Finset.mem_inter.mpr
      constructor
      · change c.vertex k ∈
          Finset.univ.image (fun i : Fin (k.val+1) => c.vertex ⟨i.val, by omega⟩)
        refine Finset.mem_image.mpr ⟨⟨k.val, by omega⟩, Finset.mem_univ _, ?_⟩
        apply congrArg c.vertex
        apply Fin.ext
        rfl
      · change c.vertex k ∈
          Finset.univ.image (fun j : Fin (c.length-k.val+1) =>
            c.vertex ⟨(k.val+j.val)%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩)
        refine Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
        apply congrArg c.vertex
        apply Fin.ext
        exact Nat.mod_eq_of_lt k.isLt

theorem arcForward_pos {G : MGraph V} (c : OccurrenceCycle G)
    (k : Fin c.length) (hk : 0 < k.val) : 1 ≤ (arcForward c k).length := by
  change 1 ≤ k.val
  omega

theorem arcWrap_pos {G : MGraph V} (c : OccurrenceCycle G)
    (k : Fin c.length) (hk : 0 < k.val) : 1 ≤ (arcWrap c k hk).length := by
  change 1 ≤ c.length-k.val
  omega

theorem arc_lengths {G : MGraph V} (c : OccurrenceCycle G)
    (k : Fin c.length) (hk : 0 < k.val) :
    (arcForward c k).length + (arcWrap c k hk).length = c.length := by
  change k.val + (c.length-k.val) = c.length
  exact Nat.add_sub_of_le (le_of_lt k.isLt)

end ThLean.W.S362

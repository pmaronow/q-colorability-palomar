module

public import ThLean.W.S370S.CodeLists
public import ThLean.W.S370S.Sizing
public import ThLean.W.S362.CycleIndex

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V] {G : MGraph V}

def listEmbedding (L : List V) (hnd : L.Nodup) {k : ℕ} (h : L.length = k) : Fin k ↪ V :=
  (finCongr h.symm).toEmbedding.trans ⟨L.get, List.nodup_iff_injective_get.mp hnd⟩

theorem listEmbedding_at (L : List V) (hnd : L.Nodup) {k : ℕ} (h : L.length = k)
    (hk : 0 < k) {i : ℕ} (hi : i < L.length) :
    codeLabel hk (listEmbedding L hnd h) i = L[i] := by
  rw [codeLabel_eq hk _ (by omega)]
  rfl

theorem listEmbedding_block (L : List V) (hnd : L.Nodup) {k : ℕ} (h : L.length = k)
    (hk : 0 < k) (pre xs post : List V) (hL : L = pre ++ xs ++ post) :
    (List.range xs.length).map
      (fun i => codeLabel hk (listEmbedding L hnd h) (pre.length+i)) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    rw [listEmbedding_at L hnd h hk (by rw [hL]; simp; omega)]
    subst L
    simp [List.getElem_append, hj,
      show ¬ pre.length+i < pre.length by omega,
      show pre.length+i < pre.length+xs.length by omega]

theorem ofFn_split_head {n : ℕ} (hn : 0 < n) (f : Fin n → V) :
    [f ⟨0,hn⟩] ++ List.ofFn (fun i : Fin (n-1) => f ⟨i.val+1,by omega⟩) =
      List.ofFn f := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    cases i with
    | zero => simp
    | succ i => simp

theorem ofFn_split_ends {n : ℕ} (hn : 0 < n) (f : Fin (n+1) → V) :
    ([f 0] ++ List.ofFn (fun i : Fin (n-1) => f ⟨i.val+1,by omega⟩)) ++
      [f (Fin.last n)] = List.ofFn f := by
  have hs := cons_range_append_eq_ofFn hn (f 0) (f (Fin.last n))
    (fun i => f ⟨(i+1)%(n+1),Nat.mod_lt _ (by omega)⟩) f rfl rfl (by
      intro i
      simp [Nat.mod_eq_of_lt (show i.val+1<n+1 by omega)])
  have hm : (List.range (n-1)).map
      (fun i => f ⟨(i+1)%(n+1),Nat.mod_lt _ (by omega)⟩) =
      List.ofFn (fun i : Fin (n-1) => f ⟨i.val+1,by omega⟩) := by
    apply map_range_eq_ofFn
    intro i
    simp [Nat.mod_eq_of_lt (show i.val+1<n+1 by omega)]
  rwa [hm] at hs

theorem toFinset_ofFn {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).toFinset = Finset.univ.image f := by
  ext x
  simp [List.mem_ofFn]

theorem append_nodup {α : Type*} [DecidableEq α] {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup) (hdis : Disjoint xs.toFinset ys.toFinset) :
    (xs++ys).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hx,hy,?_⟩
  intro a ha b hb hab
  subst b
  exact Finset.disjoint_left.mp hdis (by simpa using ha) (by simpa using hb)

theorem graph_of_two_cycles (c d : OccurrenceCycle G)
    (hdis : Disjoint (cycleOccurrences c) (cycleOccurrences d))
    (hc : cycleOccurrences c ∪ cycleOccurrences d = Finset.univ) :
    G = edgesGraph (consecutiveEdges
      (List.ofFn c.vertex ++ [c.vertex ⟨0,by have := c.length_ge_two; omega⟩]) ++
      consecutiveEdges (List.ofFn d.vertex ++ [d.vertex ⟨0,by have := d.length_ge_two; omega⟩])) := by
  have hnd : (List.ofFn c.edge ++ List.ofFn d.edge).Nodup :=
    append_nodup (List.nodup_ofFn.mpr c.edge_injective) (List.nodup_ofFn.mpr d.edge_injective)
      (by simpa only [toFinset_ofFn, cycleOccurrences] using hdis)
  have hh := edgesGraph_occurrences (List.ofFn c.edge ++ List.ofFn d.edge) hnd
    (by simpa only [List.toFinset_append, toFinset_ofFn, cycleOccurrences] using hc)
  rw [List.map_append, cycle_edgeList, cycle_edgeList] at hh
  exact hh.symm

theorem graph_of_cycles_path (c d : OccurrenceCycle G) (p : OccurrencePath G)
    (hdis : Disjoint (cycleOccurrences c) (cycleOccurrences d))
    (hpdis : Disjoint (pathOccurrences p) (cycleOccurrences c ∪ cycleOccurrences d))
    (hc : cycleOccurrences c ∪ cycleOccurrences d ∪ pathOccurrences p = Finset.univ) :
    G = edgesGraph (consecutiveEdges
      (List.ofFn c.vertex ++ [c.vertex ⟨0,by have := c.length_ge_two; omega⟩]) ++
      consecutiveEdges (List.ofFn d.vertex ++ [d.vertex ⟨0,by have := d.length_ge_two; omega⟩]) ++
      consecutiveEdges (List.ofFn p.vertex)) := by
  have hnd : (List.ofFn c.edge ++ List.ofFn d.edge).Nodup :=
    append_nodup (List.nodup_ofFn.mpr c.edge_injective) (List.nodup_ofFn.mpr d.edge_injective)
      (by simpa only [toFinset_ofFn, cycleOccurrences] using hdis)
  have hnd' : ((List.ofFn c.edge ++ List.ofFn d.edge) ++ List.ofFn p.edge).Nodup :=
    append_nodup hnd (List.nodup_ofFn.mpr p.edge_injective)
      (by simpa only [List.toFinset_append, toFinset_ofFn, cycleOccurrences, pathOccurrences] using hpdis.symm)
  have hh := edgesGraph_occurrences _ hnd'
    (by simpa only [List.toFinset_append, toFinset_ofFn, cycleOccurrences, pathOccurrences] using hc)
  rw [List.map_append, List.map_append, cycle_edgeList, cycle_edgeList, path_edgeList] at hh
  exact hh.symm

theorem rotate_at (c : OccurrenceCycle G) (a : V) (ha : a ∈ cycleVertices c) :
    ∃ d : OccurrenceCycle G, d.length = c.length ∧
      cycleVertices d = cycleVertices c ∧ cycleOccurrences d = cycleOccurrences c ∧
      d.vertex ⟨0,by have := d.length_ge_two; omega⟩ = a := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
  refine ⟨ThLean.W.S362.rotateCycle c i, rfl,
    ThLean.W.S362.rotateCycle_vertices c i, ThLean.W.S362.rotateCycle_occurrences c i, ?_⟩
  dsimp [ThLean.W.S362.rotateCycle, ThLean.W.S362.rotateIdx]
  simpa [Nat.mod_eq_of_lt i.isLt] using hi

end ThLean.W.S370S

module

public import ThLean.W.S370S.DecodeLists

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V] {G : MGraph V}

theorem decode_shared_oriented (c d : OccurrenceCycle G) (a : V)
    (hc0 : c.vertex ⟨0,by have := c.length_ge_two; omega⟩ = a)
    (hd0 : d.vertex ⟨0,by have := d.length_ge_two; omega⟩ = a)
    (hdis : Disjoint (cycleOccurrences c) (cycleOccurrences d))
    (hinter : cycleVertices c ∩ cycleVertices d = {a})
    (hcover : cycleOccurrences c ∪ cycleOccurrences d = Finset.univ) :
    ∃ (hk : 0 < (vertexSupport G).card) (v : Fin (vertexSupport G).card ↪ V),
      c.length+d.length+0 = (vertexSupport G).card+1 ∧
      G = dumbbellCode hk c.length d.length 0 v := by
  have hc := c.length_ge_two
  have hd := d.length_ge_two
  have hsize := exactDumbbell_size (G := G)
    ⟨c,d,hdis,Or.inl ⟨by rw [hinter]; simp, hcover⟩⟩
  have hedge := congrArg Finset.card hcover
  rw [Finset.card_union_of_disjoint hdis, cycleOccurrences_card,
    cycleOccurrences_card, Finset.card_univ, occurrence_card_eq_edgeCount] at hedge
  let k := (vertexSupport G).card
  have hk : 0 < k := by dsimp [k]; omega
  let T := List.ofFn (fun i : Fin (d.length-1) => d.vertex ⟨i.val+1,by omega⟩)
  let L := List.ofFn c.vertex ++ T
  have hT : T.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j hij
    have hh := congrArg (fun x : Fin d.length => x.val) (d.vertex_injective hij)
    change i.val+1 = j.val+1 at hh
    exact Fin.ext (Nat.add_right_cancel hh)
  have hsep : Disjoint (List.ofFn c.vertex).toFinset T.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (by simpa using hx)
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp (by simpa [T] using hy)
    have hxc : x ∈ cycleVertices c := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
    have hxd : x ∈ cycleVertices d := Finset.mem_image.mpr ⟨_,Finset.mem_univ _,hj⟩
    have hxa : x = a := Finset.mem_singleton.mp (hinter ▸ Finset.mem_inter.mpr ⟨hxc,hxd⟩)
    have hh := congrArg (fun x : Fin d.length => x.val)
      (d.vertex_injective (hj.trans (hxa.trans hd0.symm)))
    dsimp at hh
    omega
  have hnd : L.Nodup := append_nodup (List.nodup_ofFn.mpr c.vertex_injective) hT hsep
  have hlen : L.length = k := by
    simp only [L,T,List.length_append,List.length_ofFn]
    dsimp [k]
    omega
  let v := listEmbedding L hnd hlen
  have hfirst : (List.range c.length).map (codeLabel hk v) = List.ofFn c.vertex := by
    simpa only [List.length_nil,Nat.zero_add,List.length_ofFn] using
      listEmbedding_block L hnd hlen hk [] (List.ofFn c.vertex) T (by simp [L])
  have hsecond : (List.range (d.length-1)).map
      (fun i => codeLabel hk v (c.length+i)) = T := by
    simpa only [T,v,List.length_ofFn] using
      listEmbedding_block L hnd hlen hk (List.ofFn c.vertex) T [] (by simp [L])
  have h0 : codeLabel hk v 0 = a := by
    rw [listEmbedding_at L hnd hlen hk (by simp [L,T]; omega)]
    change (List.ofFn c.vertex ++ T)[0]'(by simp; omega) = a
    rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
    exact hc0
  have hsecondFull : [codeLabel hk v 0] ++
      (List.range (d.length-1)).map (fun i => codeLabel hk v (c.length+i)) =
      List.ofFn d.vertex := by
    rw [h0,hsecond,← hd0]
    exact ofFn_split_head (by omega) d.vertex
  refine ⟨hk,v,by omega,?_⟩
  calc
    G = edgesGraph (consecutiveEdges (List.ofFn c.vertex ++ [c.vertex ⟨0,by omega⟩]) ++
        consecutiveEdges (List.ofFn d.vertex ++ [d.vertex ⟨0,by omega⟩])) :=
      graph_of_two_cycles c d hdis hcover
    _ = dumbbellCode hk c.length d.length 0 v := by
      symm
      unfold dumbbellCode
      simp only [ite_true]
      rw [hfirst,hsecondFull,h0,hc0,hd0]

end ThLean.W.S370S

module

public import ThLean.W.S370S.DecodeLists

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V] {G : MGraph V}

theorem decode_joined_oriented (hG : ExactDumbbell G)
    (c d : OccurrenceCycle G) (p : OccurrencePath G) (a b : V)
    (hc0 : c.vertex ⟨0,by have := c.length_ge_two; omega⟩ = a)
    (hd0 : d.vertex ⟨0,by have := d.length_ge_two; omega⟩ = b)
    (hdis : Disjoint (cycleOccurrences c) (cycleOccurrences d))
    (hv : Disjoint (cycleVertices c) (cycleVertices d)) (hp : 1 ≤ p.length)
    (hfrom : PathFrom p a b)
    (hpa : pathVertices p ∩ cycleVertices c = {a})
    (hpb : pathVertices p ∩ cycleVertices d = {b})
    (hpd : Disjoint (pathOccurrences p) (cycleOccurrences c ∪ cycleOccurrences d))
    (hcover : cycleOccurrences c ∪ cycleOccurrences d ∪ pathOccurrences p = Finset.univ) :
    ∃ (hk : 0 < (vertexSupport G).card) (v : Fin (vertexSupport G).card ↪ V),
      c.length+d.length+p.length = (vertexSupport G).card+1 ∧
      G = dumbbellCode hk c.length d.length p.length v := by
  have hc := c.length_ge_two
  have hd := d.length_ge_two
  have hsize := exactDumbbell_size hG
  have hedge := congrArg Finset.card hcover
  rw [Finset.card_union_of_disjoint hpd.symm, Finset.card_union_of_disjoint hdis,
    cycleOccurrences_card, cycleOccurrences_card, pathOccurrences_card,
    Finset.card_univ, occurrence_card_eq_edgeCount] at hedge
  let k := (vertexSupport G).card
  have hk : 0 < k := by dsimp [k]; omega
  let T := List.ofFn (fun i : Fin (p.length-1) => p.vertex ⟨i.val+1,by omega⟩)
  let L := List.ofFn c.vertex ++ List.ofFn d.vertex ++ T
  have hT : T.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j hij
    have hh := congrArg (fun x : Fin (p.length+1) => x.val) (p.vertex_injective hij)
    change i.val+1 = j.val+1 at hh
    exact Fin.ext (Nat.add_right_cancel hh)
  have hcd : (List.ofFn c.vertex ++ List.ofFn d.vertex).Nodup :=
    append_nodup (List.nodup_ofFn.mpr c.vertex_injective) (List.nodup_ofFn.mpr d.vertex_injective)
      (by simpa only [toFinset_ofFn, cycleVertices] using hv)
  have hsep : Disjoint (List.ofFn c.vertex ++ List.ofFn d.vertex).toFinset T.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (by simpa [T] using hy)
    have hxp : x ∈ pathVertices p := Finset.mem_image.mpr ⟨_,Finset.mem_univ _,hi⟩
    have hx' : x ∈ List.ofFn c.vertex ++ List.ofFn d.vertex := by simpa using hx
    rcases List.mem_append.mp hx' with hx' | hx'
    · obtain ⟨j,hj⟩ := List.mem_ofFn.mp hx'
      have hxc : x ∈ cycleVertices c := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩
      have hxa : x = a := Finset.mem_singleton.mp (hpa ▸ Finset.mem_inter.mpr ⟨hxp,hxc⟩)
      have hh := congrArg (fun x : Fin (p.length+1) => x.val)
        (p.vertex_injective (hi.trans (hxa.trans hfrom.1.symm)))
      dsimp at hh
      omega
    · obtain ⟨j,hj⟩ := List.mem_ofFn.mp hx'
      have hxd : x ∈ cycleVertices d := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩
      have hxb : x = b := Finset.mem_singleton.mp (hpb ▸ Finset.mem_inter.mpr ⟨hxp,hxd⟩)
      have hh := congrArg (fun x : Fin (p.length+1) => x.val)
        (p.vertex_injective (hi.trans (hxb.trans hfrom.2.symm)))
      dsimp at hh
      omega
  have hnd : L.Nodup := by
    simpa only [L,List.append_assoc] using append_nodup hcd hT hsep
  have hlen : L.length = k := by
    simp only [L,T,List.length_append,List.length_ofFn]
    dsimp [k]
    omega
  let v := listEmbedding L hnd hlen
  have hfirst : (List.range c.length).map (codeLabel hk v) = List.ofFn c.vertex := by
    simpa only [List.length_nil,Nat.zero_add,List.length_ofFn] using
      listEmbedding_block L hnd hlen hk [] (List.ofFn c.vertex) (List.ofFn d.vertex ++ T)
        (by simp [L,List.append_assoc])
  have hsecond : (List.range d.length).map
      (fun i => codeLabel hk v (c.length+i)) = List.ofFn d.vertex := by
    simpa only [List.length_ofFn] using
      listEmbedding_block L hnd hlen hk (List.ofFn c.vertex) (List.ofFn d.vertex) T rfl
  have hthird : (List.range (p.length-1)).map
      (fun i => codeLabel hk v (c.length+d.length+i)) = T := by
    simpa only [T,v,List.length_append,List.length_ofFn] using
      listEmbedding_block L hnd hlen hk (List.ofFn c.vertex ++ List.ofFn d.vertex) T []
        (by simp [L,List.append_assoc])
  have h0 : codeLabel hk v 0 = a := by
    rw [listEmbedding_at L hnd hlen hk (by simp [L,T]; omega)]
    simpa [L,List.getElem_append,show 0<c.length by omega] using hc0
  have hatt : codeLabel hk v c.length = b := by
    rw [listEmbedding_at L hnd hlen hk (by simp [L,T]; omega)]
    simpa [L,List.getElem_append,show 0<d.length by omega] using hd0
  have hpathFull : ([codeLabel hk v 0] ++ (List.range (p.length-1)).map
      (fun i => codeLabel hk v (c.length+d.length+i))) ++ [codeLabel hk v c.length] =
      List.ofFn p.vertex := by
    rw [h0,hatt,hthird,← hfrom.1,← hfrom.2]
    exact ofFn_split_ends (by omega) p.vertex
  refine ⟨hk,v,by omega,?_⟩
  calc
    G = edgesGraph (consecutiveEdges (List.ofFn c.vertex ++ [c.vertex ⟨0,by omega⟩]) ++
        consecutiveEdges (List.ofFn d.vertex ++ [d.vertex ⟨0,by omega⟩]) ++
        consecutiveEdges (List.ofFn p.vertex)) := graph_of_cycles_path c d p hdis hpd hcover
    _ = dumbbellCode hk c.length d.length p.length v := by
      symm
      unfold dumbbellCode
      rw [if_neg (by omega)]
      try simp only [← List.append_assoc]
      rw [hfirst,hsecond,hpathFull,h0,hatt,hc0,hd0]

end ThLean.W.S370S

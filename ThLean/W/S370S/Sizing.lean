module

public import ThLean.W.S370S.Lists

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V] {G : MGraph V}

theorem cycleVertices_card (c : OccurrenceCycle G) :
    (cycleVertices c).card = c.length := by
  simp [cycleVertices, Finset.card_image_of_injective _ c.vertex_injective]

theorem cycleOccurrences_card (c : OccurrenceCycle G) :
    (cycleOccurrences c).card = c.length := by
  simp [cycleOccurrences, Finset.card_image_of_injective _ c.edge_injective]

theorem pathVertices_card (p : OccurrencePath G) :
    (pathVertices p).card = p.length+1 := by
  simp [pathVertices, Finset.card_image_of_injective _ p.vertex_injective]

theorem pathOccurrences_card (p : OccurrencePath G) :
    (pathOccurrences p).card = p.length := by
  simp [pathOccurrences, Finset.card_image_of_injective _ p.edge_injective]

theorem touches_cycle_edge (c : OccurrenceCycle G) (i : Fin c.length) (a : V)
    (ha : Touches a (c.edge i).1) : a ∈ cycleVertices c := by
  rw [c.joins, touches_pair] at ha
  rcases ha with rfl | rfl <;> simp [cycleVertices]

theorem touches_path_edge (p : OccurrencePath G) (i : Fin p.length) (a : V)
    (ha : Touches a (p.edge i).1) : a ∈ pathVertices p := by
  rw [p.joins, touches_pair] at ha
  rcases ha with rfl | rfl <;> simp [pathVertices]

theorem cycleVertices_subset_support (c : OccurrenceCycle G) :
    cycleVertices c ⊆ vertexSupport G := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  simp only [vertexSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(c.edge i).1, Nat.zero_lt_of_lt (c.edge i).2.isLt, ?_⟩
  rw [c.joins]
  exact ⟨_, rfl⟩

theorem pathVertices_subset_support (p : OccurrencePath G) (hp : 0 < p.length) :
    pathVertices p ⊆ vertexSupport G := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  simp only [vertexSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.val < p.length
  · refine ⟨(p.edge ⟨i.val, hi⟩).1, Nat.zero_lt_of_lt (p.edge ⟨i.val, hi⟩).2.isLt, ?_⟩
    rw [p.joins]
    exact ⟨_, rfl⟩
  · have he : i.val = p.length := by omega
    let j : Fin p.length := ⟨p.length-1, by omega⟩
    refine ⟨(p.edge j).1, Nat.zero_lt_of_lt (p.edge j).2.isLt, ?_⟩
    rw [p.joins, touches_pair]
    right
    congr 1
    apply Fin.ext
    dsimp [j]
    omega

theorem support_of_cycles (c d : OccurrenceCycle G)
    (hc : cycleOccurrences c ∪ cycleOccurrences d = Finset.univ) :
    vertexSupport G = cycleVertices c ∪ cycleVertices d := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨e, he, ht⟩ := (Finset.mem_filter.mp ha).2
    let o : Occurrence G := ⟨e, ⟨0, he⟩⟩
    have ho : o ∈ cycleOccurrences c ∪ cycleOccurrences d := by rw [hc]; simp
    rcases Finset.mem_union.mp ho with ho | ho
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
      exact Finset.mem_union_left _ (touches_cycle_edge c i a (by simpa [hi] using ht))
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
      exact Finset.mem_union_right _ (touches_cycle_edge d i a (by simpa [hi] using ht))
  · exact Finset.union_subset (cycleVertices_subset_support c) (cycleVertices_subset_support d)

theorem support_of_cycles_path (c d : OccurrenceCycle G) (p : OccurrencePath G)
    (hp : 0 < p.length)
    (hc : cycleOccurrences c ∪ cycleOccurrences d ∪ pathOccurrences p = Finset.univ) :
    vertexSupport G = cycleVertices c ∪ cycleVertices d ∪ pathVertices p := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨e, he, ht⟩ := (Finset.mem_filter.mp ha).2
    let o : Occurrence G := ⟨e, ⟨0, he⟩⟩
    have ho : o ∈ cycleOccurrences c ∪ cycleOccurrences d ∪ pathOccurrences p := by rw [hc]; simp
    rcases Finset.mem_union.mp ho with ho | ho
    · rcases Finset.mem_union.mp ho with ho | ho
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (touches_cycle_edge c i a (by simpa [hi] using ht)))
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (touches_cycle_edge d i a (by simpa [hi] using ht)))
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ho
      exact Finset.mem_union_right _ (touches_path_edge p i a (by simpa [hi] using ht))
  · exact Finset.union_subset
      (Finset.union_subset (cycleVertices_subset_support c) (cycleVertices_subset_support d))
      (pathVertices_subset_support p hp)

theorem occurrence_card_eq_edgeCount : Fintype.card (Occurrence G) = edgeCount G := by
  simp [Occurrence, edgeCount, Fintype.card_sigma]

theorem exactDumbbell_size (h : ExactDumbbell G) :
    2 ≤ (vertexSupport G).card ∧ edgeCount G = (vertexSupport G).card+1 := by
  obtain ⟨c, d, hdis, hcase⟩ := h
  have hmin : 2 ≤ (vertexSupport G).card :=
    c.length_ge_two.trans ((cycleVertices_card c).symm.le.trans
      (Finset.card_le_card (cycleVertices_subset_support c)))
  refine ⟨hmin, ?_⟩
  have hc := c.length_ge_two
  have hd := d.length_ge_two
  rcases hcase with ⟨hinter, hcover⟩ | ⟨hv, p, a, b, hp, hfrom, ha, hb, hpa, hpb, hpd, hcover⟩
  · have he := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hdis, cycleOccurrences_card,
      cycleOccurrences_card, Finset.card_univ, occurrence_card_eq_edgeCount] at he
    have hn := Finset.card_union_add_card_inter (cycleVertices c) (cycleVertices d)
    rw [hinter, cycleVertices_card, cycleVertices_card, ← support_of_cycles c d hcover] at hn
    omega
  · have he := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hpd.symm,
      Finset.card_union_of_disjoint hdis, cycleOccurrences_card,
      cycleOccurrences_card, pathOccurrences_card, Finset.card_univ,
      occurrence_card_eq_edgeCount] at he
    have hab : a ≠ b := by
      intro hab
      exact Finset.disjoint_left.mp hv ha (hab ▸ hb)
    have hi : (cycleVertices c ∪ cycleVertices d) ∩ pathVertices p = {a,b} := by
      rw [Finset.union_inter_distrib_right,
        Finset.inter_comm (cycleVertices c), Finset.inter_comm (cycleVertices d), hpa, hpb]
      simp
    have hn := Finset.card_union_add_card_inter (cycleVertices c ∪ cycleVertices d) (pathVertices p)
    rw [hi, Finset.card_pair hab, Finset.card_union_of_disjoint hv,
      cycleVertices_card, cycleVertices_card, pathVertices_card,
      ← support_of_cycles_path c d p (by omega) hcover] at hn
    omega

end ThLean.W.S370S

module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S365
open ThresholdFoundations

private theorem pathVertices_subset_cycleVertices_of_occurrences_subset
    {V : Type u} [Fintype V] {G : MGraph V}
    (p : OccurrencePath G) (c : OccurrenceCycle G)
    (hocc : pathOccurrences p ⊆ cycleOccurrences c)
    (hlen : 1 ≤ p.length) : pathVertices p ⊆ cycleVertices c := by
  intro x hx
  simp only [pathVertices, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨i, rfl⟩ := hx
  have hiBound : i.val ≤ p.length := Nat.lt_succ_iff.mp i.isLt
  have hplen : 0 < p.length := lt_of_lt_of_le (by decide) hlen
  have hcpos : 0 < c.length := lt_of_lt_of_le (by decide) c.length_ge_two
  have hedge : ∃ j : Fin p.length, p.vertex i ∈ (p.edge j).1 := by
    by_cases hlt : i.val < p.length
    · let j : Fin p.length := ⟨i.val, hlt⟩
      have hi : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (p.length + 1)) = i :=
        Fin.ext rfl
      refine ⟨j, ?_⟩
      rw [p.joins j, hi]
      exact Sym2.mem_mk_left _ _
    · have heq : i.val = p.length := by omega
      let j : Fin p.length := ⟨i.val - 1, by
        rw [heq]
        exact Nat.sub_lt hplen (by decide)⟩
      have hi : (⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ : Fin (p.length + 1)) = i :=
        Fin.ext (by dsimp [j]; omega)
      refine ⟨j, ?_⟩
      rw [p.joins j, hi]
      exact Sym2.mem_mk_right _ _
  obtain ⟨j, hj⟩ := hedge
  have hjocc : p.edge j ∈ pathOccurrences p := by
    simp [pathOccurrences]
  have hjcycle : p.edge j ∈ cycleOccurrences c := hocc hjocc
  simp only [cycleOccurrences, Finset.mem_image, Finset.mem_univ, true_and] at hjcycle
  obtain ⟨k, heq⟩ := hjcycle
  have hmem : p.vertex i ∈ (c.edge k).1 := by
    rw [heq]
    exact hj
  rw [c.joins k] at hmem
  simp only [Sym2.mem_iff] at hmem
  rcases hmem with hmem | hmem
  · simp only [cycleVertices, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨k, hmem.symm⟩
  · simp only [cycleVertices, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨(k.val + 1) % c.length, Nat.mod_lt _ hcpos⟩, hmem.symm⟩

theorem S3_62Statement_of_deps (h59 : ThLean.BP.S3.S3_59Statement.{u}) :
    ThLean.BP.S3.S3_62Statement.{u} := by
  intro V inst G c p a b hp hne hpath ha hb hvertices hdisjoint
  obtain ⟨r, s, hrlen, hslen, hrpath, hspath, hrsocc, hrsunion, hrsvertices, _⟩ :=
    h59 V G c a b ha hb hne
  have hroccSub : pathOccurrences r ⊆ cycleOccurrences c := by
    rw [← hrsunion]
    exact Finset.subset_union_left
  have hsoccSub : pathOccurrences s ⊆ cycleOccurrences c := by
    rw [← hrsunion]
    exact Finset.subset_union_right
  have hrvertsSub := pathVertices_subset_cycleVertices_of_occurrences_subset r c hroccSub hrlen
  have hsvertsSub := pathVertices_subset_cycleVertices_of_occurrences_subset s c hsoccSub hslen
  have hrpOcc : Disjoint (pathOccurrences r) (pathOccurrences p) := by
    rw [Finset.disjoint_left]
    intro e he hrp
    have hec : e ∈ cycleOccurrences c := by
      rw [← hrsunion]
      exact Finset.mem_union_left _ he
    exact (Finset.disjoint_left.mp hdisjoint) hrp hec
  have hspOcc : Disjoint (pathOccurrences s) (pathOccurrences p) := by
    rw [Finset.disjoint_left]
    intro e he hsp
    have hec : e ∈ cycleOccurrences c := by
      rw [← hrsunion]
      exact Finset.mem_union_right _ he
    exact (Finset.disjoint_left.mp hdisjoint) hsp hec
  have hrvertsP : pathVertices r ∩ pathVertices p ⊆ {a, b} := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxr, hxp⟩
    have hxc : x ∈ cycleVertices c := hrvertsSub hxr
    have hxab : x ∈ pathVertices p ∩ cycleVertices c := Finset.mem_inter.mpr ⟨hxp, hxc⟩
    simpa [hvertices] using hxab
  have hsvertsP : pathVertices s ∩ pathVertices p ⊆ {a, b} := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxs, hxp⟩
    have hxc : x ∈ cycleVertices c := hsvertsSub hxs
    have hxab : x ∈ pathVertices p ∩ cycleVertices c := Finset.mem_inter.mpr ⟨hxp, hxc⟩
    simpa [hvertices] using hxab
  refine ⟨a, b, hne, r, s, p, ?_, ?_⟩
  · intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hrlen, hrpath⟩
    · exact ⟨hslen, hspath⟩
    · exact ⟨hp, hpath⟩
  · rw [List.pairwise_cons]
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact ⟨hrsocc, by simp [hrsvertices]⟩
      · exact ⟨hrpOcc, hrvertsP⟩
    · rw [List.pairwise_cons]
      constructor
      · intro x hx
        simp at hx
        subst x
        exact ⟨hspOcc, hsvertsP⟩
      · exact List.pairwise_singleton _ _

end ThLean.W.S365

import ThLean.W.S364S.WalkConnector

noncomputable section
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S364S

open ThresholdFoundations ThLean.BP.S3

variable {V : Type*}

/-- Both endpoints of an occurrence of a cycle are vertices of that cycle. -/
theorem endpoints_mem_cycle {K : MGraph V} (c : OccurrenceCycle K)
    {e : Occurrence K} (he : e ∈ cycleOccurrences c) {a b : V}
    (hab : e.1 = s(a,b)) : a ∈ cycleVertices c ∧ b ∈ cycleVertices c := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  have hpair := hab.symm.trans (c.joins i)
  have hi : c.vertex i ∈ cycleVertices c := Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  have hj : c.vertex ⟨(i.val + 1) % c.length, Nat.mod_lt _ (by have := c.length_ge_two; omega)⟩
      ∈ cycleVertices c := Finset.mem_image.mpr ⟨_, by simp, rfl⟩
  rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hi, hj⟩
  · exact ⟨hj, hi⟩

/-- Two vertex-disjoint cycles in a connected occurrence graph admit a positive-length
connecting path that meets each cycle only at its endpoint and uses no cycle occurrence. -/
theorem S3_61ConnectorStatement_holds :
    ThLean.Contrib.S364.S3_61ConnectorStatement.{u} := by
  intro V _ K _ hconn c d hdisj
  have hc : (cycleVertices c).Nonempty := by
    refine ⟨c.vertex ⟨0, by have := c.length_ge_two; omega⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨_, by simp, rfl⟩
  have hd : (cycleVertices d).Nonempty := by
    refine ⟨d.vertex ⟨0, by have := d.length_ge_two; omega⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨_, by simp, rfl⟩
  obtain ⟨a, b, w, ha, hb, hw, hpos, hfirst, hlast⟩ :=
    shortestPath_between hconn (cycleVertices c) (cycleVertices d) hc hd hdisj
  let p := occurrencePathOfWalk w hw
  have hfrom : PathFrom p a b := pathFrom_occurrencePathOfWalk w hw
  have hpc : pathVertices p ∩ cycleVertices c = {a} := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨i, _, hix⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
      change w.getVert i.val = x at hix
      have hi : w.getVert i.val ∈ cycleVertices c := by
        rw [hix]
        exact (Finset.mem_inter.mp hx).2
      have hi0 := hfirst i.val (Nat.le_of_lt_succ i.isLt) hi
      have hxa : x = a := by
        simpa [hi0] using hix.symm
      exact Finset.mem_singleton.mpr hxa
    · intro hx
      have hxa := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨⟨0, by omega⟩, by simp, hfrom.1⟩, ha⟩
  have hpd : pathVertices p ∩ cycleVertices d = {b} := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨i, _, hix⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
      change w.getVert i.val = x at hix
      have hi : w.getVert i.val ∈ cycleVertices d := by
        rw [hix]
        exact (Finset.mem_inter.mp hx).2
      have hin := hlast i.val (Nat.le_of_lt_succ i.isLt) hi
      have hxb : x = b := by
        simpa [hin] using hix.symm
      exact Finset.mem_singleton.mpr hxb
    · intro hx
      have hxb := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨⟨p.length, by omega⟩, by simp, hfrom.2⟩, hb⟩
  have hedge : Disjoint (pathOccurrences p) (cycleOccurrences c ∪ cycleOccurrences d) := by
    apply Finset.disjoint_left.mpr
    intro e hep hecd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hep
    rcases Finset.mem_union.mp hecd with hec | hed
    · obtain ⟨hx, hy⟩ := endpoints_mem_cycle c hec (p.joins i)
      have hx0 := hfirst i.val (by have := i.isLt; change i.val < w.length at this; omega) hx
      have hy0 := hfirst (i.val + 1) (by have := i.isLt; change i.val < w.length at this; omega) hy
      omega
    · obtain ⟨hx, hy⟩ := endpoints_mem_cycle d hed (p.joins i)
      have hxn := hlast i.val (by have := i.isLt; change i.val < w.length at this; omega) hx
      have hyn := hlast (i.val + 1) (by have := i.isLt; change i.val < w.length at this; omega) hy
      omega
  exact ⟨p, a, b, hpos, hfrom, ha, hb, hpc, hpd, hedge⟩

end ThLean.W.S364S

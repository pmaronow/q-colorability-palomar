module

public import ThLean.Contrib.S364.S3_61Connector

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S364
open ThresholdFoundations

theorem S3_61Statement_of_connector
    (hConnector : ThLean.Contrib.S364.S3_61ConnectorStatement.{u}) :
    ThLean.BP.S3.S3_61Statement.{u} := by
  intro V _ K hK hconn c d hEdges hCard
  have hcycle : DumbbellIn K := by
    by_cases hDisj : Disjoint (cycleVertices c) (cycleVertices d)
    · obtain ⟨p, a, b, hpos, hfrom, ha, hb, hic, hid, hedge⟩ :=
        hConnector V K hK hconn c d hDisj
      exact ⟨c, d, hEdges,
        Or.inr ⟨hDisj, ⟨p, a, b, hpos, hfrom, ha, hb, hic, hid, hedge⟩⟩⟩
    · have hne : (cycleVertices c ∩ cycleVertices d) ≠ ∅ := by
        intro hempty
        apply hDisj
        refine Finset.disjoint_left.mpr ?_
        intro x hx hy
        have hxmem : x ∈ cycleVertices c ∩ cycleVertices d :=
          Finset.mem_inter.mpr ⟨hx, hy⟩
        rw [hempty] at hxmem
        simp at hxmem
      have hpos : 0 < (cycleVertices c ∩ cycleVertices d).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      have hone : (cycleVertices c ∩ cycleVertices d).card = 1 := by omega
      exact ⟨c, d, hEdges, Or.inl hone⟩
  refine ⟨hcycle, ?_⟩
  intro hDisj
  obtain ⟨p, a, b, hpos, hfrom, ha, hb, hic, hid, hedge⟩ :=
    hConnector V K hK hconn c d hDisj
  exact ⟨p, a, b, hpos, hfrom, hic, hid, hedge⟩

end ThLean.W.S364

module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.Contrib.S364
open ThresholdFoundations

/-- The graph-theoretic connector needed in the disjoint-cycle case of
`lem:pre-cycles(b)`: in a connected support, two vertex-disjoint cycles can
be joined by a path that meets them only at its endpoints. -/
def S3_61ConnectorStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (K : MGraph V), Loopless K →
  (ThLean.BP.S3.graphSupport K).Connected →
  ∀ c d : OccurrenceCycle K,
    Disjoint (cycleVertices c) (cycleVertices d) →
    ∃ (p : OccurrencePath K) (a b : V), 1 ≤ p.length ∧ PathFrom p a b ∧
      a ∈ cycleVertices c ∧ b ∈ cycleVertices d ∧
      pathVertices p ∩ cycleVertices c = {a} ∧
      pathVertices p ∩ cycleVertices d = {b} ∧
      Disjoint (pathOccurrences p) (cycleOccurrences c ∪ cycleOccurrences d)

end ThLean.Contrib.S364

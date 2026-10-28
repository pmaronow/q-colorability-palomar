import ThLean.BP.S3.Cycles

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.Contrib.S368
open ThresholdFoundations ThLean.BP.S3

/-- A connected, noncolorable component together with a transport of all the
structural data needed by the obstruction argument. This isolates component
extraction and transport from the rest of S3-65. -/
def HasBadConnectedComponent {V : Type u} [Fintype V] (q : ℕ)
    (G : MGraph V) : Prop :=
  ∃ (S : Finset V) (H : MGraph {v : V // v ∈ S})
    (lift : MGraph {v : V // v ∈ S} → MGraph V),
    2 ≤ Fintype.card {v : V // v ∈ S} ∧
    Fintype.card {v : V // v ∈ S} ≤ Fintype.card V ∧
    Loopless H ∧
    (graphSupport H).Connected ∧
    ¬ Colorable q H ∧
    (∀ F : MGraph {v : V // v ∈ S}, subgraph F H → subgraph (lift F) G) ∧
    (∀ F : MGraph {v : V // v ∈ S}, Loopless F → Loopless (lift F)) ∧
    (∀ F : MGraph {v : V // v ∈ S}, edgeCount (lift F) = edgeCount F) ∧
    (∀ F : MGraph {v : V // v ∈ S},
      (vertexSupport (lift F)).card = (vertexSupport F).card) ∧
    (∀ F : MGraph {v : V // v ∈ S}, ExactTheta F → ExactTheta (lift F)) ∧
    (∀ F : MGraph {v : V // v ∈ S}, ExactDumbbell F → ExactDumbbell (lift F))

end ThLean.Contrib.S368

import ThLean.BP.S3.Adapters

noncomputable section
open scoped BigOperators
universe u
namespace ThLean.Contrib.S392
open ThresholdFoundations

/-- Restricting a connected multigraph to its occurring vertices preserves support connectivity. -/
def S3_57bConnectedStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (G : MGraph V),
    ConnectedSupport G →
    (ThLean.BP.S3.graphSupport (inducedGraph G (vertexSupport G))).Connected

/-- A theta witness in the support restriction lifts along the subtype inclusion. -/
def S3_57bThetaStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (G : MGraph V),
    ThetaIn (inducedGraph G (vertexSupport G)) → ThetaIn G

/-- A dumbbell witness in the support restriction lifts along the subtype inclusion. -/
def S3_57bDumbbellStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (G : MGraph V),
    DumbbellIn (inducedGraph G (vertexSupport G)) → DumbbellIn G

end ThLean.Contrib.S392

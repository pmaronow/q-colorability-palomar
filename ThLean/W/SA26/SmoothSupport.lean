module

public import ThLean.BP.SA.Interpolation

@[expose] public section

noncomputable section
open scoped BigOperators Topology

namespace ThLean.W.SA26

open ThLean.BP.SA
open ThresholdFoundations

theorem SA_I12dStatement_holds : ThLean.BP.SA.SA_I12dStatement := by
  intro D hD F r
  unfold supportMean poissonSupportMean poissonSupportWeight
  fun_prop

end ThLean.W.SA26

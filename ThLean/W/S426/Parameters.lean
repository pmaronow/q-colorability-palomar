module

public import ThLean.BP.S4.Parameters

@[expose] public section

namespace ThLean.W.S426

theorem S4_PAR_01BStatement_holds :
    ThLean.BP.S4.S4_PAR_01BStatement := by
  intro q _
  rw [ThresholdFoundations.capDensity]
  linarith

end ThLean.W.S426

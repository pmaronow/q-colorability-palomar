import ThLean.W.BR01.PairBridge

namespace ThLean.W.BR01S

/-- B00, reusing the complete proof from the earlier BR01 attempt. -/
theorem PairBridgeStatement_holds : ThresholdFoundations.PairBridgeStatement :=
  ThLean.W.BR01.PairBridgeStatement_holds

example : ThresholdFoundations.PairBridgeStatement := PairBridgeStatement_holds

end ThLean.W.BR01S

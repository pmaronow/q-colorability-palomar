module

public import ThLean.W.BR01.PairBridge

@[expose] public section

namespace ThLean.W.BR01S

/-- B00: the pair representations agree, and valid simple-model denominators are positive.
The proof is `ThLean.W.BR01.PairBridgeStatement_holds`. -/
theorem PairBridgeStatement_holds : ThresholdFoundations.PairBridgeStatement :=
  ThLean.W.BR01.PairBridgeStatement_holds

example : ThresholdFoundations.PairBridgeStatement := PairBridgeStatement_holds

end ThLean.W.BR01S

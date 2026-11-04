module

public import ThLean.W.S364S.Connector

@[expose] public section

universe u

namespace ThLean.W.S364S

/-- Joining disjoint cycles into a dumbbell, at the original blueprint type. -/
theorem S3_61Statement_holds : ThLean.BP.S3.S3_61Statement.{u} :=
  ThLean.W.S364.S3_61Statement_of_connector S3_61ConnectorStatement_holds

end ThLean.W.S364S

import ThLean.Defs

namespace ThLean.Contrib.S436

/-- The upstream lifetime contract required by S4 bridge 03A. -/
def PreLifetimeDependencyStatement : Prop :=
  ThresholdFoundations.PreLifetimeStatement.{0}

end ThLean.Contrib.S436

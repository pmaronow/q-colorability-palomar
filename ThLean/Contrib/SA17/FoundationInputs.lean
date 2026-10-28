import ThLean.BP.SA.Basics

/-! Foundation contracts required to extend the upper quantile tail past the cap. -/
namespace ThLean.Contrib.SA17

def SA_F02FoundationInputsStatement : Prop :=
  ThresholdFoundations.PreQuantileStatement ∧
    ThresholdFoundations.ProjectiveConsistencyStatement

end ThLean.Contrib.SA17

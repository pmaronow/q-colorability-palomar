module

public import ThLean.BP.S3.Centre

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `sec:pre`; blueprint P1-77. -/
def S3_77Statement : Prop :=
  S3_08Statement.{u} ∧ S3_13Statement.{u, v} ∧ S3_20Statement.{u} ∧ S3_29Statement.{u, v} ∧
  S3_30Statement.{u} ∧ S3_38AStatement.{u} ∧ S3_41Statement ∧ S3_51Statement ∧
  S3_64Statement.{u} ∧ S3_76Statement.{u} ∧ S3_03Statement.{u, v} ∧ S3_05Statement.{u} ∧
  S3_07Statement.{u} ∧ S3_23Statement.{u} ∧ S3_24Statement.{u} ∧ S3_36Statement.{u} ∧
  S3_36SStatement.{u} ∧ S3_39Statement.{u} ∧ S3_54Statement.{u} ∧ S3_70Statement.{u} ∧ S3_74Statement.{u}

theorem S3_77_assembly
    (h08 : S3_08Statement.{u}) (h13 : S3_13Statement.{u, v}) (h20 : S3_20Statement.{u})
    (h29 : S3_29Statement.{u, v}) (h30 : S3_30Statement.{u}) (h38 : S3_38AStatement.{u})
    (h41 : S3_41Statement) (h51 : S3_51Statement) (h64 : S3_64Statement.{u})
    (h76 : S3_76Statement.{u}) (h03 : S3_03Statement.{u, v}) (h05 : S3_05Statement.{u})
    (h07 : S3_07Statement.{u}) (h23 : S3_23Statement.{u}) (h24 : S3_24Statement.{u})
    (h36 : S3_36Statement.{u}) (h36S : S3_36SStatement.{u}) (h39 : S3_39Statement.{u})
    (h54 : S3_54Statement.{u}) (h70 : S3_70Statement.{u}) (h74 : S3_74Statement.{u}) :
    S3_77Statement.{u, v} :=
  ⟨h08,h13,h20,h29,h30,h38,h41,h51,h64,h76,h03,h05,h07,h23,h24,h36,h36S,h39,h54,h70,h74⟩

end ThLean.BP.S3

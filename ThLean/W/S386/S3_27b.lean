module

public import ThLean.BP.S3.Adapters

@[expose] public section

noncomputable section
open scoped ENNReal
universe u

namespace ThLean.W.S386

open ThresholdFoundations

theorem S3_27bStatement_of_deps
    (h27 : ThLean.BP.S3.S3_27Statement.{u}) :
    ThLean.BP.S3.S3_27bStatement.{u} := by
  intro V _ q hq hV G hκ
  have h := (h27 V q hq hV).1 G hκ
  rcases h with ⟨_, hfinite, hreal⟩
  calc
    lifetime q G = ENNReal.ofReal (lifetimeReal q G) := by
      rw [lifetimeReal]
      exact (ENNReal.ofReal_toReal hfinite).symm
    _ ≤ ENNReal.ofReal (1 / kappa q G) := ENNReal.ofReal_le_ofReal hreal

example (h27 : ThLean.BP.S3.S3_27Statement.{u}) :
    ThLean.BP.S3.S3_27bStatement.{u} :=
  S3_27bStatement_of_deps h27

end ThLean.W.S386

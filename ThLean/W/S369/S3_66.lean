import ThLean.W.S369.ThetaEncoding
import ThLean.Contrib.S369.Theta

noncomputable section
universe u
namespace ThLean.W.S369
open ThresholdFoundations
open ThLean.BP.S3
open ThLean.Contrib.S369

/-- The S3 theta encoding leaf, conditional on its three explicit structural gaps. -/
theorem S3_66Statement_from_gaps
    (hdecode : ThetaExactDecodeStatement.{u})
    (hcodeExact : ThetaCodeExactStatement.{u})
    (hcodeSupport : ThetaCodeSupportStatement.{u}) :
    ThLean.BP.S3.S3_66Statement.{u} := by
  intro V inst
  constructor
  · exact hdecode V
  · intro k hk j₁ j₂ j₃ v hk2 hj₁ hj₂ hj₃ hsum
    refine ⟨hcodeExact V k hk j₁ j₂ j₃ v hk2 hj₁ hj₂ hj₃ hsum,
      hcodeSupport V k hk j₁ j₂ j₃ v hk2 hj₁ hj₂ hj₃ hsum, ?_⟩
    exact thetaCode_edgeCount hk j₁ j₂ j₃ v hj₁ hj₂ hj₃ hsum

end ThLean.W.S369

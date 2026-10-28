import ThLean.Contrib.S541.Occupation

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S541

/-- Assemble the exact leaf from the root-reduction and Poisson-contraction
contracts, with the specified Section 5 dependencies available. -/
theorem S5_32Statement_from_helpers
    (hroot : ThLean.Contrib.S541.S5_32RootPoissonReductionStatement)
    (hweight : ThLean.Contrib.S541.S5_32PoissonWeightContractionStatement)
    (h03 : ThLean.BP.S5.S5_03Statement)
    (h06 : ThLean.BP.S5.S5_06Statement)
    (h09B : ThLean.BP.S5.S5_09BStatement)
    (hRelabel : ThresholdFoundations.PreRelabelStatement.{0, 0})
    (hE01 : ThLean.BP.S5.S5_E01Statement)
    (hE08 : ThLean.BP.S5.S5_E08Statement) :
    ThLean.BP.S5.S5_32Statement := by
  intro q n D hq hn a t ht
  exact ⟨hroot h03 h09B hRelabel hE01 hE08 q n D hq hn a t ht,
    hweight h06 hE01 q n D hq hn t ht⟩

example (hroot : ThLean.Contrib.S541.S5_32RootPoissonReductionStatement)
    (hweight : ThLean.Contrib.S541.S5_32PoissonWeightContractionStatement)
    (h03 : ThLean.BP.S5.S5_03Statement)
    (h06 : ThLean.BP.S5.S5_06Statement)
    (h09B : ThLean.BP.S5.S5_09BStatement)
    (hRelabel : ThresholdFoundations.PreRelabelStatement.{0, 0})
    (hE01 : ThLean.BP.S5.S5_E01Statement)
    (hE08 : ThLean.BP.S5.S5_E08Statement) :
    ThLean.BP.S5.S5_32Statement := S5_32Statement_from_helpers
      hroot hweight h03 h06 h09B hRelabel hE01 hE08

end ThLean.W.S541

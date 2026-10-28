import ThLean.BP.S5.Identification
import ThLean.Contrib.S523.S5_20Helpers

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S523
open ThLean.BP.S5
open ThLean.Contrib.S523

/-- The leaf follows from its two remaining split and measurability obligations. -/
theorem S5_20Statement_from_helpers
    (hsplit : S5_20SplitBoundStatement)
    (hmeas : S5_20MeasurabilityStatement) : S5_20Statement := by
  intro q N hq hN Z hZ hNZ
  exact ⟨hsplit q N hq hN Z hZ hNZ,
    (hmeas q N hq hN Z hZ hNZ).1,
    (hmeas q N hq hN Z hZ hNZ).2⟩

example (hsplit : S5_20SplitBoundStatement)
    (hmeas : S5_20MeasurabilityStatement) :
    ThLean.BP.S5.S5_20Statement := S5_20Statement_from_helpers hsplit hmeas

end ThLean.W.S523

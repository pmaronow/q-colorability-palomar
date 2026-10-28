import ThLean.Contrib.S390.PoissonSplit

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v

namespace ThLean.W.S390
open ThresholdFoundations ThLean.BP.S3 ThLean.Contrib.S390

set_option maxHeartbeats 1000000

/-- Assemble the fixed-time split identity from the ordered-word splitting
and the ordered-word/uniform-edge model bridge.
-/
theorem S3_37cStatement_of_helpers
    (hGraphList : S390GraphListENNStatement.{max u v})
    (hSplitWord : S390SplitWordENNStatement.{u, v}) :
    S3_37cStatement.{u, v} := by
  intro A B instA instB hTotal hB t h ht
  letI : DecidableEq (A ⊕ B) := Classical.decEq (A ⊕ B)
  have hTwo : 2 ≤ Fintype.card (A ⊕ B) := by omega
  rw [← hGraphList (A ⊕ B) hTwo t h ht]
  exact hSplitWord A B hTotal hB t h ht

end ThLean.W.S390

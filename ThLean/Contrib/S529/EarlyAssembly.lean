import ThLean.BP.S5.Identification

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal

namespace ThLean.Contrib.S529
open ThLean.BP.S5 ThresholdFoundations

/-- The remaining averaging and integration step in the early-time split. -/
def S5_26AEarlyIntegralAssemblyStatement : Prop :=
  ∀ q N D k : ℕ, 3 ≤ q → lowSizeOnset q ≤ N → 1 ≤ D → 4 * D ≤ N →
  Real.exp 1 * D * lowMeanBound q < (k : ℝ) →
    (∫ s in (0 : ℝ)..lowTimeCap q N, discrepancy q N D s) ≤
      (∫ s in (0 : ℝ)..lowTimeCap q N,
        lowEdgeRate N * (D.choose 2 : ℝ) * s) +
      (∫ s in (0 : ℝ)..lowTimeCap q N,
        ∑' j : ℕ, if k < j then
          poissonWeight (D * neighborMean N D s) j else 0) +
      uniformMean (fun Z : UniformSubset (Fin N) D =>
        ∫ s in (0 : ℝ)..lowTimeCap q N,
          (D : ℝ)^k * addedFailure (V := {v : Fin N // v ∉ Z.val}) q
            (lowEdgeRate N * s) (neighborMean N D s))

end ThLean.Contrib.S529

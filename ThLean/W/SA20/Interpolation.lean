import ThLean.BP.SA.Interpolation
import ThLean.Contrib.SA20.Histogram

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA20
open ThresholdFoundations ThLean.BP.SA

theorem SA_I11aStatement_of_histogram
    (hcount : ThLean.Contrib.SA20.CountHistogramStatement)
    (hproduct : ThLean.Contrib.SA20.PoissonProductFactorStatement) :
    SA_I11aStatement := by
  intro D _ _ _ ν μ hν hsum z
  let K : ℕ := ∑ e : D, z e
  let A : ℕ → ℝ := fun k =>
    ∑ x : Fin k → D,
      (∏ i, ν (x i)) * indicator (∀ e, (List.ofFn x).count e = z e)
  have hA (k : ℕ) : A k =
      if K = k then
        ((Nat.factorial k : ℝ) / ∏ e : D, (Nat.factorial (z e) : ℝ)) *
          ∏ e : D, ν e ^ z e
      else 0 := by
    simpa [A, K] using hcount D ν k z
  have hzero (k : ℕ) (hk : k ≠ K) : A k = 0 := by
    rw [hA k]
    simp [K, Ne.symm hk]
  have hseries : (∑' k : ℕ, poissonWeight μ k * A k) =
      poissonWeight μ K * A K := by
    exact tsum_eq_single K (by
      intro k hk
      simp [hzero k hk])
  rw [weightedListMean, poissonMixture]
  change (∑' k : ℕ, poissonWeight μ k * A k) = _
  rw [hseries, hA K]
  simpa [K] using hproduct D ν μ z hsum

end ThLean.W.SA20

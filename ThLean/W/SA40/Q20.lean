import ThLean.Contrib.SA40.Q20

noncomputable section
open scoped BigOperators
namespace ThLean.W.SA40
open ThresholdFoundations

theorem SA_Q20Statement_from_helpers
    (hSurvival : ThLean.Contrib.SA40.Q20ProcessSurvivalUnitIntervalStatement)
    (hBridge : ThLean.Contrib.SA40.Q20LoopSplitBridgeStatement)
    (hPoisson : PrePoissonStatement) : ThLean.BP.SA.SA_Q20Statement := by
  intro q n hq hn c hc
  let μ : ℝ := c * ((n : ℝ) - 1)
  have hμ : 0 ≤ μ := by
    dsimp [μ]
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    positivity
  have hWeights := hPoisson.1 μ hμ
  have hMixSummable : Summable (fun j : ℕ =>
      poissonWeight μ j * processSurvival (V := Fin n) q j) := by
    apply hWeights.1.of_nonneg_of_le
    · intro j
      exact mul_nonneg (hWeights.2.2 j) (hSurvival q n hq hn j).1
    · intro j
      calc
        poissonWeight μ j * processSurvival (V := Fin n) q j ≤
            poissonWeight μ j * 1 :=
          mul_le_mul_of_nonneg_left (hSurvival q n hq hn j).2 (hWeights.2.2 j)
        _ = poissonWeight μ j := by ring
  have hMixNonneg :
      0 ≤ poissonMixture μ (processSurvival (V := Fin n) q) := by
    rw [poissonMixture]
    apply tsum_nonneg
    intro j
    exact mul_nonneg (hWeights.2.2 j) (hSurvival q n hq hn j).1
  have hMixLe :
      poissonMixture μ (processSurvival (V := Fin n) q) ≤ 1 := by
    rw [poissonMixture]
    calc
      (∑' j : ℕ, poissonWeight μ j * processSurvival (V := Fin n) q j) ≤
          ∑' j : ℕ, poissonWeight μ j * 1 := by
        exact hMixSummable.tsum_le_tsum
          (fun j => mul_le_mul_of_nonneg_left (hSurvival q n hq hn j).2
            (hWeights.2.2 j))
          (by simpa using hWeights.1)
      _ = 1 := by simpa [mul_one] using hWeights.2.1
  refine ⟨?_, hMixNonneg, hMixLe, ?_⟩
  · simpa [μ] using hMixSummable
  · simpa [μ] using hBridge q n hq hn c hc

end ThLean.W.SA40

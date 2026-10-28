import ThLean.BP.S3.Poisson

noncomputable section
open scoped BigOperators

namespace ThLean.W.S332

open ThresholdFoundations

private theorem exp_series_hasSum (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

private theorem poissonWeight_summable (z : ℝ) : Summable (poissonWeight z) := by
  have hs := (Real.summable_pow_div_factorial z).mul_left (Real.exp (-z))
  apply hs.congr
  intro k
  simp [poissonWeight, div_eq_mul_inv, mul_assoc]

private theorem poissonWeight_hasSum (z : ℝ) :
    HasSum (poissonWeight z) (Real.exp (-z) * Real.exp z) := by
  have hs := (exp_series_hasSum z).mul_left (Real.exp (-z))
  convert hs using 1
  · funext k
    simp [poissonWeight, div_eq_mul_inv, mul_assoc]

private theorem poissonWeight_gen_summable (z a : ℝ) :
    Summable (fun k : ℕ => poissonWeight z k * a ^ k) := by
  have hs := (Real.summable_pow_div_factorial (z * a)).mul_left (Real.exp (-z))
  apply hs.congr
  intro k
  simp only [poissonWeight]
  rw [mul_pow]
  ring

private theorem poissonWeight_gen_hasSum (z a : ℝ) :
    HasSum (fun k : ℕ => poissonWeight z k * a ^ k)
      (Real.exp (-z) * Real.exp (z * a)) := by
  have hs := (exp_series_hasSum (z * a)).mul_left (Real.exp (-z))
  convert hs using 1
  · funext k
    simp only [poissonWeight]
    rw [mul_pow]
    ring

theorem S3_31Statement_holds : ThLean.BP.S3.S3_31Statement := by
  intro z hz
  refine ⟨?_, poissonWeight_summable z, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp [poissonWeight]
    positivity
  · have h := (poissonWeight_hasSum z).tsum_eq
    rw [h]
    rw [← Real.exp_add]
    simp
  · intro a ha
    refine ⟨poissonWeight_gen_summable z a, ?_⟩
    have h := (poissonWeight_gen_hasSum z a).tsum_eq
    rw [h, ← Real.exp_add]
    congr 1
    ring
  · intro k
    by_cases hk : k = 0
    · simp [poissonWeight, hk]
    · simp [poissonWeight, hk]
  · intro hzpos k
    dsimp [poissonWeight]
    positivity

example : ThLean.BP.S3.S3_31Statement := S3_31Statement_holds

end ThLean.W.S332

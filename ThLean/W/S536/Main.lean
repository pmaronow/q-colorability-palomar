import ThLean.BP.S5.Main

noncomputable section
open Real
open ThresholdFoundations

namespace ThLean.W.S536

theorem S5_40AStatement_holds : ThLean.BP.S5.S5_40AStatement := by
  constructor
  · intro q hq
    have hq1 : 1 ≤ (q : ℝ) := by
      exact_mod_cast (show 1 ≤ q by omega)
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
    unfold lowBoundConstant identificationConstant lifetimeConstant lowMeanBound
    positivity
  · intro q n hq hn y hy
    dsimp only
    let N : ℝ := (n : ℝ)
    have hN6 : 6 ≤ N := by
      dsimp [N]
      exact_mod_cast (show 6 ≤ n by omega)
    have hNpos : 0 < N := by dsimp [N]; exact_mod_cast (show 0 < n by omega)
    have hden : 0 < (N - 1) * (N - 2) := by
      apply mul_pos <;> linarith
    have hcoef0 : 0 ≤ 2 * N ^ 2 / ((N - 1) * (N - 2)) := by
      positivity
    have hpoly : 2 * N ^ 2 ≤ 4 * ((N - 1) * (N - 2)) := by
      have hprod : 0 ≤ (N - 6) * N := mul_nonneg (by linarith) (le_of_lt hNpos)
      nlinarith [hprod]
    have hcoef : 2 * N ^ 2 / ((N - 1) * (N - 2)) ≤ 4 := by
      exact (div_le_iff₀ hden).2 (by nlinarith [hpoly])
    have hq1 : 1 ≤ (q : ℝ) := by
      exact_mod_cast (show 1 ≤ q by omega)
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
    have hA : 0 < 1 + lifetimeConstant q := by
      unfold lifetimeConstant
      positivity
    have hId : 0 < identificationConstant q := by
      unfold identificationConstant lowMeanBound
      positivity
    have hYpow : 0 ≤ y ^ (-(1 / 2 : ℝ)) := by positivity
    have hSqrtInv : (Real.sqrt y)⁻¹ = y ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hy) (1 / 2 : ℝ), ← Real.sqrt_eq_rpow]
    have hSqrt : Real.sqrt ((1 + lifetimeConstant q) / y) =
        Real.sqrt (1 + lifetimeConstant q) * y ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_div (le_of_lt hA), div_eq_mul_inv, hSqrtInv]
    have hNpow : 0 ≤ N ^ (3 / 8 : ℝ) := by positivity
    constructor
    · positivity
    · rw [hSqrt]
      change
        (2 * N ^ 2 / ((N - 1) * (N - 2)) *
            (Real.sqrt (1 + lifetimeConstant q) * y ^ (-(1 / 2 : ℝ)))) *
          (2 * identificationConstant q * N ^ (3 / 8 : ℝ)) ≤
        lowBoundConstant q * y ^ (-(1 / 2 : ℝ)) * N ^ (3 / 8 : ℝ)
      calc
        _ = (2 * N ^ 2 / ((N - 1) * (N - 2)) *
              (Real.sqrt (1 + lifetimeConstant q) * y ^ (-(1 / 2 : ℝ)))) *
              (2 * identificationConstant q * N ^ (3 / 8 : ℝ)) := by ring
        _ ≤ (4 * (Real.sqrt (1 + lifetimeConstant q) * y ^ (-(1 / 2 : ℝ)))) *
              (2 * identificationConstant q * N ^ (3 / 8 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hcoef (by positivity)
          · positivity
        _ = (4 * Real.sqrt (1 + lifetimeConstant q) * y ^ (-(1 / 2 : ℝ))) *
              (2 * identificationConstant q * N ^ (3 / 8 : ℝ)) := by ring
        _ = lowBoundConstant q * y ^ (-(1 / 2 : ℝ)) * N ^ (3 / 8 : ℝ) := by
          unfold lowBoundConstant
          ring

example : ThLean.BP.S5.S5_40AStatement := S5_40AStatement_holds

end ThLean.W.S536

import ThLean.BP.S5.Identification
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal

namespace ThLean.W.S526

open ThresholdFoundations

theorem S5_23Statement_holds : ThLean.BP.S5.S5_23Statement := by
  intro q N D hq hN hD hDN
  have hNreal : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have hNne1 : N ≠ 1 := by omega
    exact sub_ne_zero.mpr (by exact_mod_cast hNne1)
  have hcoef :
      lowEdgeRate N * (D.choose 2 : ℝ) =
        (D : ℝ) * ((D : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) := by
    rw [lowEdgeRate, Nat.cast_choose_two, Nat.cast_choose_two]
    field_simp [hNreal, hNm1]
  have hIntegral :
      (∫ s in (0 : ℝ)..lowTimeCap q N,
        lowEdgeRate N * (D.choose 2 : ℝ) * s) =
        (D : ℝ) * ((D : ℝ) - 1) * (lowTimeCap q N)^2 /
          (2 * (N : ℝ) * ((N : ℝ) - 1)) := by
    rw [hcoef, intervalIntegral.integral_const_mul, integral_id]
    field_simp [hNreal, hNm1]
    ring
  have hsecond :
      (D : ℝ) * ((D : ℝ) - 1) * (lowTimeCap q N)^2 /
          (2 * (N : ℝ) * ((N : ℝ) - 1)) =
        2 * (q : ℝ)^2 * (Real.log (q : ℝ))^2 *
          (D : ℝ) * ((D : ℝ) - 1) * (N : ℝ) / ((N : ℝ) - 1) := by
    dsimp [lowTimeCap]
    field_simp [hNreal, hNm1]
  constructor
  · exact hIntegral
  constructor
  · exact hsecond
  · rw [hIntegral]
    have hfactor :
        (D : ℝ) * ((D : ℝ) - 1) * (N : ℝ) / ((N : ℝ) - 1) ≤
          (D : ℝ)^2 := by
      have hden : 0 < (N : ℝ) - 1 := by
        have : 1 < N := by omega
        exact sub_pos.mpr (by exact_mod_cast this)
      rw [div_le_iff₀ hden]
      have hDreal : (0 : ℝ) ≤ D := by positivity
      have hDNreal : (D : ℝ) ≤ N := by exact_mod_cast hDN
      nlinarith
    have hscale :
        0 ≤ 2 * (q : ℝ)^2 * (Real.log (q : ℝ))^2 := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hfactor hscale
    rw [hsecond]
    convert hmul using 1; ring

end ThLean.W.S526

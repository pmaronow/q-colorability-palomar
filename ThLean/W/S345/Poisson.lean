import ThLean.BP.S3.Poisson
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace ThLean.W.S345

/-- The polynomial-exponential integral is the Gamma integral at a natural argument. -/
theorem S3_40GStatement_holds : ThLean.BP.S3.S3_40GStatement := by
  intro m
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have hn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hint := integrableOn_rpow_mul_exp_neg_rpow (s := (m : ℝ)) (p := (1 : ℝ)) hm one_pos
  have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (m : ℝ) + 1) (r := (1 : ℝ)) (by positivity) one_pos
  have hint' : IntegrableOn (fun s : ℝ => s ^ m * Real.exp (-s)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using hint
  have hintegral : (∫ s : ℝ in Ioi 0, s ^ m * Real.exp (-s)) = (m.factorial : ℝ) := by
    simpa only [one_mul, neg_mul, one_div, inv_one, Real.one_rpow, Nat.cast_add,
      Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast,
      Real.Gamma_nat_eq_factorial] using hgamma
  exact ⟨hint', hlim, hintegral⟩

end ThLean.W.S345

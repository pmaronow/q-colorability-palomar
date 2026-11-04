module

public import ThLean.BP.S5.Elementary
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace ThLean.W.S513

theorem S5_E07Statement_holds : ThLean.BP.S5.S5_E07Statement := by
  constructor
  · intro m p hp
    have hm : 0 < (m : ℝ) + 1 := by positivity
    have hbase : IntegrableOn
        (fun t : ℝ => t ^ ((m : ℝ) + 1 - 1) * Real.exp (-(p * t))) (Ioi 0) := by
      apply Integrable.of_integral_ne_zero
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hm hp]
      positivity
    have hfun : (fun t : ℝ => ThresholdFoundations.poissonWeight (p * t) m) =
        (fun t : ℝ => (p ^ m / (m.factorial : ℝ)) *
          (t ^ ((m : ℝ) + 1 - 1) * Real.exp (-(p * t)))) := by
      funext t
      simp only [ThresholdFoundations.poissonWeight, div_eq_mul_inv, mul_pow]
      rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring, Real.rpow_natCast]
      ring
    have hIoi : IntegrableOn
        (fun t : ℝ => ThresholdFoundations.poissonWeight (p * t) m) (Ioi 0) := by
      rw [hfun]
      exact hbase.const_mul _
    constructor
    · exact (integrableOn_Ici_iff_integrableOn_Ioi).2 hIoi
    · rw [integral_Ici_eq_integral_Ioi, hfun, integral_const_mul]
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hm hp, Real.Gamma_nat_eq_factorial]
      have hpow : (1 / p : ℝ) ^ ((m : ℝ) + 1) = (1 / p) ^ (m + 1) := by
        rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
      rw [hpow]
      field_simp [hp.ne']
      rw [pow_succ, one_div_pow]
      field_simp [hp.ne']
  · intro c a hc ha
    constructor
    · exact (integrableOn_Ici_iff_integrableOn_Ioi).2
        (integrableOn_exp_mul_Ioi (by linarith) a)
    · rw [integral_Ici_eq_integral_Ioi,
        integral_exp_mul_Ioi (by linarith : -c < 0) a]
      field_simp [hc.ne']

end ThLean.W.S513

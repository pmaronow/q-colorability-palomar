import ThLean.BP.S3.Tails
import Mathlib.Analysis.SpecialFunctions.Stirling

noncomputable section

namespace ThLean.W.S349

open ThLean.BP.S3

/-- Factorial and binomial coefficient estimates from the preliminary tail lemma. -/
theorem S3_42Statement_holds : ThLean.BP.S3.S3_42Statement := by
  constructor
  · intro k hk
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hrad : 1 ≤ 2 * Real.pi * (k : ℝ) := by
      have hpi : 3 < Real.pi := Real.pi_gt_three
      have hmul : 2 * Real.pi ≤ 2 * Real.pi * (k : ℝ) := by
        simpa using mul_le_mul_of_nonneg_left hkR (by positivity : 0 ≤ 2 * Real.pi)
      nlinarith
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := Real.one_le_sqrt.mpr hrad
    have hst := Stirling.le_factorial_stirling k
    have hbase : 0 ≤ ((k : ℝ) / Real.exp 1) ^ k := by positivity
    calc
      ((k : ℝ) / Real.exp 1) ^ k ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) *
          ((k : ℝ) / Real.exp 1) ^ k := by nlinarith
      _ ≤ (k.factorial : ℝ) := hst
  constructor
  · intro m k hk
    constructor
    · exact Nat.choose_le_pow_div (α := ℝ) k m
    · have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
      have hmR : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      have hfac : ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
        have h := Stirling.le_factorial_stirling k
        have hkR1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have hrad : 1 ≤ 2 * Real.pi * (k : ℝ) := by
          have hmul : 2 * Real.pi ≤ 2 * Real.pi * (k : ℝ) := by
            simpa using mul_le_mul_of_nonneg_left hkR1 (by positivity : 0 ≤ 2 * Real.pi)
          nlinarith [Real.pi_gt_three]
        have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := Real.one_le_sqrt.mpr hrad
        have hnonneg : 0 ≤ ((k : ℝ) / Real.exp 1) ^ k := by positivity
        exact le_trans (by nlinarith) h
      have hdiv : (m : ℝ) ^ k / (k.factorial : ℝ) ≤
          (m : ℝ) ^ k / ((k : ℝ) / Real.exp 1) ^ k :=
        div_le_div_of_nonneg_left (pow_nonneg hmR k)
          (pow_pos (div_pos hkR he) k) hfac
      calc
        (m : ℝ) ^ k / (k.factorial : ℝ) ≤
            (m : ℝ) ^ k / ((k : ℝ) / Real.exp 1) ^ k := hdiv
        _ = ((m : ℝ) / ((k : ℝ) / Real.exp 1)) ^ k := by
          rw [← div_pow]
        _ = (Real.exp 1 * (m : ℝ) / (k : ℝ)) ^ k := by
          have hbase : (m : ℝ) / ((k : ℝ) / Real.exp 1) =
              Real.exp 1 * (m : ℝ) / (k : ℝ) := by
            field_simp [ne_of_gt hkR, ne_of_gt he]
          rw [hbase]
  · intro a b
    have hdvd : a.factorial * b.factorial ∣ (a + b).factorial :=
      Nat.factorial_mul_factorial_dvd_factorial_add a b
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (a + b)) hdvd

end ThLean.W.S349

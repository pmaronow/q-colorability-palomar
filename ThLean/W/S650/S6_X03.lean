import ThLean.BP.S6.Analytic

noncomputable section

namespace ThLean.W.S650

theorem S6_X03Statement_holds : ThLean.BP.S6.S6_X03Statement := by
  intro m k hk
  constructor
  · exact Nat.choose_le_pow_div (α := ℝ) k m
  · have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    have hseries : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp (k : ℝ) :=
      Real.pow_div_factorial_le_exp _ (by positivity) _
    have hexp : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
      simp
    have hmul : 0 ≤ ((m : ℝ) / (k : ℝ)) ^ k :=
      pow_nonneg (div_nonneg (by positivity) hkpos.le) _
    have hcancel :
        ((m : ℝ) / (k : ℝ)) ^ k * (k : ℝ) ^ k = (m : ℝ) ^ k := by
      rw [div_pow]
      field_simp [ne_of_gt hkpos]
    calc
      (m : ℝ) ^ k / (k.factorial : ℝ) =
          (((m : ℝ) / (k : ℝ)) ^ k * (k : ℝ) ^ k) /
            (k.factorial : ℝ) := by rw [hcancel]
      _ = ((m : ℝ) / (k : ℝ)) ^ k *
            ((k : ℝ) ^ k / (k.factorial : ℝ)) := by ring
      _ ≤ ((m : ℝ) / (k : ℝ)) ^ k * Real.exp (k : ℝ) :=
        mul_le_mul_of_nonneg_left hseries hmul
      _ = (Real.exp 1 * (m : ℝ) / (k : ℝ)) ^ k := by
        rw [hexp, ← mul_pow]
        congr 1
        ring

end ThLean.W.S650

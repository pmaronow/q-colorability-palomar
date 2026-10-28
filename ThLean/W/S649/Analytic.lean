import ThLean.BP.S6.Analytic

namespace ThLean.W.S649

/-- The factorial lower bound follows from the reciprocal exponential-series bound X01. -/
theorem S6_X02Statement_of_deps
    (hX01 : ThLean.BP.S6.S6_X01Statement) :
    ThLean.BP.S6.S6_X02Statement := by
  intro k hk
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hkR
  have hkpowpos : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkpos _
  have hX := hX01.2 (k : ℝ) k hkpos
  have hmul := mul_le_mul_of_nonneg_right hX hkpowpos.le
  have hfact : (k : ℝ) ^ k * Real.exp (-(k : ℝ)) ≤ (k.factorial : ℝ) := by
    calc
      (k : ℝ) ^ k * Real.exp (-(k : ℝ)) =
          Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by ring
      _ ≤ (k.factorial : ℝ) / (k : ℝ) ^ k * (k : ℝ) ^ k := hmul
      _ = (k.factorial : ℝ) := by field_simp [ne_of_gt hkpowpos]
  have hexpPow : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    simp
  calc
    ((k : ℝ) / Real.exp 1) ^ k = (k : ℝ) ^ k / (Real.exp 1) ^ k := by
      rw [div_pow]
    _ = (k : ℝ) ^ k / Real.exp (k : ℝ) := by rw [← hexpPow]
    _ = (k : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero (k : ℝ)]
    _ ≤ (k.factorial : ℝ) := hfact

example (hX01 : ThLean.BP.S6.S6_X01Statement) :
    ThLean.BP.S6.S6_X02Statement := S6_X02Statement_of_deps hX01

end ThLean.W.S649

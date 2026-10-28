import ThLean.BP.S5.Elementary

noncomputable section

namespace ThLean.W.S508

theorem S5_E03Statement_holds : ThLean.BP.S5.S5_E03Statement := by
  intro k hk
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hfactorial : 0 < (Nat.factorial k : ℝ) := by positivity
  have hexp : (k : ℝ) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (k : ℝ) :=
    Real.pow_div_factorial_le_exp (k : ℝ) hkpos.le k
  have hexp_mul : (k : ℝ) ^ k ≤ Real.exp (k : ℝ) * (Nat.factorial k : ℝ) :=
    (div_le_iff₀ hfactorial).mp hexp
  have hexp_nat : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    simp
  rw [hexp_nat] at hexp_mul
  have hden : 0 < (Real.exp 1 : ℝ) ^ k := pow_pos (Real.exp_pos 1) _
  constructor
  · positivity
  · calc
      ((k : ℝ) / Real.exp 1) ^ k = (k : ℝ) ^ k / (Real.exp 1 : ℝ) ^ k := by
        rw [div_pow]
      _ ≤ (Nat.factorial k : ℝ) := by
        apply (div_le_iff₀ hden).2
        nlinarith [hexp_mul]

end ThLean.W.S508

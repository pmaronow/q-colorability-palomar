import ThLean.BP.S5.Elementary

noncomputable section
open scoped BigOperators

namespace ThLean.W.S511

open ThresholdFoundations

theorem S5_E06AStatement_holds : ThLean.BP.S5.S5_E06AStatement := by
  intro a b ha hb m
  have hterm : ∀ j : ℕ, j ≤ m →
      poissonWeight a j * poissonWeight b (m - j) =
        Real.exp (-(a + b)) *
          ((m.choose j : ℝ) * a ^ j * b ^ (m - j)) / (m.factorial : ℝ) := by
    intro j hj
    have hfacNat := Nat.choose_mul_factorial_mul_factorial hj
    have hfac : (m.choose j : ℝ) * (j.factorial : ℝ) *
        ((m - j).factorial : ℝ) = (m.factorial : ℝ) := by
      exact_mod_cast hfacNat
    have hden : (1 / (j.factorial : ℝ)) *
        (1 / ((m - j).factorial : ℝ)) =
          (m.choose j : ℝ) / (m.factorial : ℝ) := by
      have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
      have hkf : ((m - j).factorial : ℝ) ≠ 0 := by positivity
      have hmf : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      nlinarith [hfac]
    unfold poissonWeight
    rw [neg_add, Real.exp_add]
    calc
      (Real.exp (-a) * a ^ j / (j.factorial : ℝ)) *
          (Real.exp (-b) * b ^ (m - j) / ((m - j).factorial : ℝ)) =
        Real.exp (-a) * Real.exp (-b) * a ^ j * b ^ (m - j) *
          ((1 / (j.factorial : ℝ)) * (1 / ((m - j).factorial : ℝ)) : ℝ) := by ring
      _ = Real.exp (-a) * Real.exp (-b) * a ^ j * b ^ (m - j) *
          ((m.choose j : ℝ) / (m.factorial : ℝ)) := by rw [hden]
      _ = Real.exp (-a) * Real.exp (-b) *
          ((m.choose j : ℝ) * a ^ j * b ^ (m - j)) / (m.factorial : ℝ) := by ring
  calc
    ∑ j ∈ Finset.range (m + 1), poissonWeight a j * poissonWeight b (m - j) =
        ∑ j ∈ Finset.range (m + 1),
          Real.exp (-(a + b)) *
            ((m.choose j : ℝ) * a ^ j * b ^ (m - j)) / (m.factorial : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = ∑ j ∈ Finset.range (m + 1),
        (Real.exp (-(a + b)) / (m.factorial : ℝ)) *
          ((m.choose j : ℝ) * a ^ j * b ^ (m - j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = Real.exp (-(a + b)) / (m.factorial : ℝ) *
        ∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * a ^ j * b ^ (m - j) := by
          rw [← Finset.mul_sum]
    _ = Real.exp (-(a + b)) * (a + b) ^ m / (m.factorial : ℝ) := by
          rw [add_pow]
          ring
    _ = poissonWeight (a + b) m := by
          rfl

end ThLean.W.S511

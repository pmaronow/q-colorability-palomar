module

public import ThLean.BP.S6.Analytic

@[expose] public section

namespace ThLean.W.S634

open ThLean.BP.S6
open ThresholdFoundations

theorem S6_31bStatement_of_deps (hX04 : S6_X04Statement) : S6_31bStatement := by
  intro n Λ j hn hΛ hj
  let m : ℕ := cap Λ n - 1
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) < (3 : ℝ) := by norm_num
    exact this.trans_le (by exact_mod_cast hn)
  have hp0 : 0 ≤ (2 : ℝ) / n := by positivity
  have hp1 : (2 : ℝ) / n ≤ 1 := by
    rw [div_le_one hnpos]
    exact_mod_cast (show 2 ≤ n by omega)
  have hparts := (hX04 m j (2 / (n : ℝ)) hj hp0 hp1).2
  have htail := hparts.1.trans hparts.2
  have hfloor : (cap Λ n : ℝ) ≤ Λ * n := by
    exact Nat.floor_le (mul_nonneg (le_of_lt hΛ) (by positivity))
  have hmle : (m : ℝ) ≤ Λ * n := by
    have hmcap : (m : ℝ) ≤ (cap Λ n : ℝ) := by
      exact_mod_cast (show m ≤ cap Λ n from Nat.sub_le _ _)
    exact hmcap.trans hfloor
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase : Real.exp 1 * (m : ℝ) * (2 / (n : ℝ)) / (j : ℝ) ≤
      2 * Real.exp 1 * Λ / (j : ℝ) := by
    calc
      Real.exp 1 * (m : ℝ) * (2 / (n : ℝ)) / (j : ℝ)
          ≤ Real.exp 1 * (Λ * n) * (2 / (n : ℝ)) / (j : ℝ) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hjpos)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hmle (le_of_lt hepos)) (by positivity)
      _ = 2 * Real.exp 1 * Λ / (j : ℝ) := by
        field_simp [ne_of_gt hnpos, ne_of_gt hjpos]
  have hbase0 : 0 ≤ Real.exp 1 * (m : ℝ) * (2 / (n : ℝ)) / (j : ℝ) := by positivity
  calc
    ThLean.BP.S6.binomialTail m (2 / (n : ℝ)) j ≤
        (Real.exp 1 * (m : ℝ) * (2 / (n : ℝ)) / (j : ℝ)) ^ j := htail
    _ ≤ (2 * Real.exp 1 * Λ / (j : ℝ)) ^ j := pow_le_pow_left₀ hbase0 hbase j

end ThLean.W.S634

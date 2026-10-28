import ThLean.BP.S4.Parameters

noncomputable section

namespace ThLean.W.S428

open ThresholdFoundations

private theorem log_three_gt_one : 1 < Real.log (3 : ℝ) := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
  exact Real.exp_one_lt_three

private theorem log_nat_gt_one {n : ℕ} (hn : 3 ≤ n) :
    1 < Real.log (n : ℝ) := by
  have hcast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hcast
  linarith [log_three_gt_one]

theorem S4_PAR_03Statement_holds : ThLean.BP.S4.S4_PAR_03Statement := by
  constructor
  · intro n
    by_cases hn : n < 3
    · simp [ThresholdFoundations.epsilon, hn]
    · have hn3 : 3 ≤ n := Nat.le_of_not_gt hn
      have hlog : 1 < Real.log (n : ℝ) := log_nat_gt_one hn3
      have hlogpos : 0 < Real.log (n : ℝ) := by linarith
      have hpos : 0 < Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ) / 2) :=
        Real.rpow_pos_of_pos hlogpos _
      have hle : Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ) / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hlog) (by norm_num)
      simpa [ThresholdFoundations.epsilon, hn] using And.intro hpos hle
  · intro i j hij
    by_cases hi : i < 3
    · by_cases hj : j < 3
      · simp [ThresholdFoundations.epsilon, hi, hj]
      · have hj3 : 3 ≤ j := Nat.le_of_not_gt hj
        have hlog : 1 < Real.log (j : ℝ) := log_nat_gt_one hj3
        have hle : Real.rpow (Real.log (j : ℝ)) (-(3 : ℝ) / 2) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hlog) (by norm_num)
        simpa [ThresholdFoundations.epsilon, hi, hj] using hle
    · have hi3 : 3 ≤ i := Nat.le_of_not_gt hi
      have hj3 : 3 ≤ j := hi3.trans hij
      have hlogi : 1 < Real.log (i : ℝ) := log_nat_gt_one hi3
      have hlogj : 1 < Real.log (j : ℝ) := log_nat_gt_one hj3
      have hlogs : Real.log (i : ℝ) ≤ Real.log (j : ℝ) := by
        apply Real.log_le_log (by exact_mod_cast (by omega : 0 < i))
        exact_mod_cast hij
      have hpow := Real.rpow_le_rpow_of_nonpos (by linarith [hlogi]) hlogs
        (by norm_num : (-(3 : ℝ) / 2) ≤ 0)
      simpa [ThresholdFoundations.epsilon, hi, Nat.not_lt.mpr hj3] using hpow

end ThLean.W.S428

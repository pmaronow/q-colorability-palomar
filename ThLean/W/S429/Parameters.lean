module

public import ThLean.BP.S4.Parameters

@[expose] public section

noncomputable section

namespace ThLean.W.S429

open ThresholdFoundations

theorem S4_PAR_04Statement_holds : ThLean.BP.S4.S4_PAR_04Statement := by
  intro k hk
  let n : ℕ := Nat.floor (Real.exp (k : ℝ))
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hprev : (1 : ℝ) ≤ (k : ℝ) - 1 := by linarith [hkR]
  have hexp2 : 4 < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  have hexpmono : Real.exp 2 ≤ Real.exp (k : ℝ) :=
    Real.exp_le_exp.mpr hkR
  have h3real : (3 : ℝ) ≤ Real.exp (k : ℝ) := by
    nlinarith [hexp2, hexpmono]
  have hn3 : 3 ≤ n := by
    dsimp [n]
    exact Nat.le_floor h3real
  have hexp_split : Real.exp (k : ℝ) =
      Real.exp ((k : ℝ) - 1) * Real.exp 1 := by
    calc
      Real.exp (k : ℝ) = Real.exp (((k : ℝ) - 1) + 1) := by congr 1; ring
      _ = Real.exp ((k : ℝ) - 1) * Real.exp 1 := Real.exp_add _ _
  have hprev_pos : 0 < Real.exp ((k : ℝ) - 1) := Real.exp_pos _
  have hprev_ge1 : 1 ≤ Real.exp ((k : ℝ) - 1) :=
    Real.one_le_exp_iff.mpr (by linarith)
  have hexp_gap : Real.exp ((k : ℝ) - 1) + 1 ≤ Real.exp (k : ℝ) := by
    rw [hexp_split]
    calc
      Real.exp ((k : ℝ) - 1) + 1 ≤ 2 * Real.exp ((k : ℝ) - 1) := by
        nlinarith [hprev_ge1]
      _ ≤ Real.exp ((k : ℝ) - 1) * Real.exp 1 := by
        nlinarith [mul_le_mul_of_nonneg_left Real.exp_one_gt_two.le
          (le_of_lt hprev_pos)]
  have hfloor_lower : Real.exp ((k : ℝ) - 1) ≤ (n : ℝ) := by
    have hfloor : Real.exp (k : ℝ) < (n : ℝ) + 1 := by
      dsimp [n]
      exact Nat.lt_floor_add_one _
    linarith
  have hlog : (k : ℝ) - 1 ≤ Real.log (n : ℝ) := by
    have hlog' := Real.log_le_log (Real.exp_pos _) hfloor_lower
    simpa only [Real.log_exp] using hlog'
  have heps : epsilon n =
      Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ) / 2) := by
    simp [epsilon, show ¬ n < 3 by omega]
  refine ⟨hn3, hfloor_lower, ?_⟩
  rw [heps]
  exact Real.rpow_le_rpow_of_nonpos (by linarith [hprev_pos]) hlog (by norm_num)

end ThLean.W.S429

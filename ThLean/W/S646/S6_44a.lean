import ThLean.BP.S6.Analytic

noncomputable section

namespace ThLean.W.S646

open ThLean.BP.S6

theorem S6_44aStatement_holds : ThLean.BP.S6.S6_44aStatement := by
  intro n Λ hΛ hcut
  change max 3 (Nat.ceil (Real.exp (analyticCutoff Λ ^ 4))) ≤ n at hcut
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hcut
  have hceil : Nat.ceil (Real.exp (analyticCutoff Λ ^ 4)) ≤ n :=
    (le_max_right _ _).trans hcut
  have hexp : Real.exp (analyticCutoff Λ ^ 4) ≤ (n : ℝ) :=
    Nat.le_of_ceil_le hceil
  have hpow : analyticCutoff Λ ^ 4 ≤ Real.log (n : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hexp
  have hT : 0 ≤ analyticCutoff Λ := by
    unfold analyticCutoff
    positivity
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ analyticCutoff Λ ^ 4)
    hpow (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have heq : analyticCutoff Λ = (analyticCutoff Λ ^ 4) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast_mul hT 4 (1 / 4 : ℝ)]
    norm_num
  have hroot : analyticCutoff Λ ≤ fourthLog n := by
    calc
      analyticCutoff Λ = (analyticCutoff Λ ^ 4) ^ (1 / 4 : ℝ) := heq
      _ ≤ (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) := hr
      _ = fourthLog n := rfl
  exact ⟨hn3, hroot⟩

end ThLean.W.S646

module

public import ThLean.BP.S5.Main

@[expose] public section

noncomputable section

namespace ThLean.W.S534

open ThLean.BP.S5 ThresholdFoundations

theorem S5_37Statement_holds : ThLean.BP.S5.S5_37Statement := by
  intro q n hq hn hon
  have hnNat : 0 < n := by omega
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hn16Real : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexpOne : Real.exp 1 < (n : ℝ) := by
    exact lt_of_lt_of_le (lt_trans Real.exp_one_lt_three (by norm_num)) hn16Real
  have hlognOne : 1 < Real.log (n : ℝ) := by
    simpa using Real.log_lt_log (Real.exp_pos 1) hexpOne
  have hlognPos : 0 < Real.log (n : ℝ) := by linarith
  have hloglogPos : 0 < Real.log (Real.log (n : ℝ)) :=
    Real.log_pos hlognOne
  have hdegreeNonneg : 0 ≤ (degreeCut n : ℝ) := by positivity
  have hdegreeLe : (degreeCut n : ℝ) ≤ (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) := by
    dsimp [degreeCut]
    exact Nat.floor_le (by positivity)
  have htruncUpper : (lowTruncation n : ℝ) ≤
      Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) + 1 := by
    dsimp [lowTruncation]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hExpIdentity : Real.log (Real.log (n : ℝ)) *
        ((1 / 4 : ℝ) *
          (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) + 1)) =
      Real.log (n : ℝ) * (1 / 4 : ℝ) +
        Real.log (Real.log (n : ℝ)) * (1 / 4 : ℝ) := by
    field_simp [ne_of_gt hloglogPos]
  have hfirst : (degreeCut n : ℝ) ^ (lowTruncation n) ≤
      (n : ℝ) ^ (1 / 4 : ℝ) * (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) := by
    calc
      (degreeCut n : ℝ) ^ (lowTruncation n) =
          (degreeCut n : ℝ) ^ (lowTruncation n : ℝ) := by
            rw [← Real.rpow_natCast]
      _ ≤ ((Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) ^ (lowTruncation n : ℝ) :=
        Real.rpow_le_rpow hdegreeNonneg hdegreeLe (by positivity)
      _ = (Real.log (n : ℝ)) ^ ((1 / 4 : ℝ) * (lowTruncation n : ℝ)) := by
        rw [← Real.rpow_mul hlognPos.le]
      _ ≤ (Real.log (n : ℝ)) ^
          ((1 / 4 : ℝ) *
            (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) + 1)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        nlinarith
      _ = (n : ℝ) ^ (1 / 4 : ℝ) * (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_def_of_pos hlognPos,
          Real.rpow_def_of_pos hnReal,
          Real.rpow_def_of_pos hlognPos,
          ← Real.exp_add, hExpIdentity]
  have hsquare : (degreeCut n : ℝ) ^ 2 ≤
      ((Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) ^ 2 := by
    have hprod : 0 ≤
        ((Real.log (n : ℝ)) ^ (1 / 4 : ℝ) - (degreeCut n : ℝ)) *
          ((Real.log (n : ℝ)) ^ (1 / 4 : ℝ) + (degreeCut n : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hdegreeLe) (by positivity)
    nlinarith
  have hsquareIdentity : ((Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) ^ 2 =
      (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlognPos.le]
    norm_num
  exact ⟨hfirst, hsquare.trans_eq hsquareIdentity⟩

end ThLean.W.S534

example : ThLean.BP.S5.S5_37Statement :=
  ThLean.W.S534.S5_37Statement_holds

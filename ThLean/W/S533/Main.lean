module

public import ThLean.BP.S5.Main

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S533
open ThresholdFoundations

theorem S5_36Statement_holds : ThLean.BP.S5.S5_36Statement := by
  intro q n hq hn hon
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hexpq : Real.exp 1 < (q : ℝ) := by
    exact lt_of_lt_of_le Real.exp_one_lt_three (by exact_mod_cast (show 3 ≤ q by omega))
  have hlogqgt1 : (1 : ℝ) < Real.log (q : ℝ) :=
    (Real.lt_log_iff_exp_lt hqpos).2 hexpq
  have hceilq : 4 * q + 1 ≤ Nat.ceil (4 * (q : ℝ) * Real.log (q : ℝ)) := by
    rw [Nat.add_one_le_ceil_iff]
    have hdiff : 0 < (q : ℝ) * Real.log (q : ℝ) - (q : ℝ) := by
      have := mul_pos hqpos (sub_pos.mpr hlogqgt1)
      nlinarith
    push_cast
    nlinarith [hdiff]
  have honsetlower : 4 * q + 2 ≤ lowSizeOnset q := by
    dsimp [lowSizeOnset]
    omega
  have hqsmall : 2 * q < n - 1 := by omega
  have hn1 : (1 : ℝ) < (n : ℝ) := by norm_cast; omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hexpn : Real.exp 1 < (n : ℝ) := by
    exact lt_trans Real.exp_one_lt_three (by norm_cast; omega)
  have hloggt1 : (1 : ℝ) < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hnpos).2 hexpn
  have hloglogpos : 0 < Real.log (Real.log (n : ℝ)) :=
    Real.log_pos hloggt1
  have hqrange : 2 * q + 1 ≤ n := by omega
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := hlogpos.le
  have hlogbound : Real.log (n : ℝ) ≤ (n : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hnpos
  have hnc : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hncube : (16 : ℝ)^3 ≤ (n : ℝ)^3 := by
    gcongr
  have hcube : (4096 : ℝ) ≤ (n : ℝ)^3 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcube (le_of_lt hnpos)
  have hbig : (n : ℝ) - 1 ≤ (n : ℝ)^4 / 4096 := by nlinarith
  have hlogpow : Real.log (n : ℝ) ≤ (n : ℝ)^4 / 4096 := hlogbound.trans hbig
  have hroot : (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) ≤ (n : ℝ) / 8 := by
    have hmono := Real.rpow_le_rpow hlognonneg hlogpow (by norm_num : 0 ≤ (1 / 4 : ℝ))
    have hid : ((n : ℝ)^4 / 4096) ^ (1 / 4 : ℝ) = (n : ℝ) / 8 := by
      have heq : (n : ℝ)^4 / 4096 = ((n : ℝ) / 8)^4 := by ring
      rw [heq]
      convert Real.pow_rpow_inv_natCast (show 0 ≤ (n : ℝ) / 8 by positivity)
        (by norm_num : (4 : ℕ) ≠ 0) using 1
      norm_num
    exact hmono.trans_eq hid
  have hDbase : (1 : ℝ) ≤ Real.log (n : ℝ) := hloggt1.le
  have hDfloor : 1 ≤ degreeCut n := by
    rw [degreeCut, Nat.one_le_floor_iff]
    exact Real.one_le_rpow hDbase (by norm_num)
  have hDfloorle : (degreeCut n : ℝ) ≤ (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) := by
    dsimp [degreeCut]
    exact Nat.floor_le (Real.rpow_nonneg (le_of_lt hlogpos) _)
  have hDreal : 4 * (degreeCut n : ℝ) ≤ (n : ℝ) - 1 := by
    calc
      4 * (degreeCut n : ℝ) ≤ 4 * ((n : ℝ) / 8) := by nlinarith [hDfloorle, hroot]
      _ ≤ (n : ℝ) - 1 := by nlinarith [hn1]
  have hDplusReal : 4 * (degreeCut n : ℝ) + 1 ≤ (n : ℝ) := by
    linarith [hDreal]
  have hDplusNat : 4 * degreeCut n + 1 ≤ n := by
    exact_mod_cast hDplusReal
  have hDrange : 4 * degreeCut n ≤ n - 1 := by omega
  have hratioPos : 0 < Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) :=
    div_pos hlogpos hloglogpos
  have hklower : Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤ (lowTruncation n : ℝ) := by
    dsimp [lowTruncation]
    exact Nat.le_ceil _
  have hktrunc : 1 ≤ lowTruncation n := by
    rw [lowTruncation, Nat.one_le_ceil_iff]
    exact hratioPos
  have hknonneg : 0 ≤ Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := hratioPos.le
  have hkupper : (lowTruncation n : ℝ) ≤ Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) + 1 := by
    dsimp [lowTruncation]
    have hc : ((Nat.ceil (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) : ℕ) : ℝ) ≤
        (Nat.floor (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one _
    have hf : (Nat.floor (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) : ℝ) ≤
        Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := Nat.floor_le hknonneg
    linarith
  exact ⟨hqrange, hDfloor, hDrange, hlogpos, hloglogpos, hktrunc, hklower, hkupper⟩

end ThLean.W.S533

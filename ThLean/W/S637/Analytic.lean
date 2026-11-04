module

public import ThLean.BP.S6.Analytic

@[expose] public section

noncomputable section
open ThresholdFoundations
namespace ThLean.W.S637

open ThLean.BP.S6

theorem S6_33Statement_holds : ThLean.BP.S6.S6_33Statement := by
  intro n Λ hn hΛ
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hnsub : 0 < (n : ℝ) - 1 := by linarith
  have hexp : Real.exp 1 < (n : ℝ) := by
    exact lt_of_lt_of_le Real.exp_one_lt_three hnR
  have hlog : 1 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hnpos).2 hexp
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have htpos : 0 < fourthLog n := by
    unfold fourthLog
    exact Real.rpow_pos_of_pos hlogpos _
  have htone : 1 < fourthLog n := by
    unfold fourthLog
    exact Real.one_lt_rpow hlog (by norm_num)
  have hroot : fourthLog n ^ 4 = Real.log (n : ℝ) := by
    unfold fourthLog
    convert Real.rpow_inv_natCast_pow (le_of_lt hlogpos)
      (by norm_num : (4 : ℕ) ≠ 0) using 1 <;> norm_num
  have hDpos : 1 ≤ degreeCut n := by
    unfold degreeCut
    exact_mod_cast (Nat.floor_pos.mpr htone.le)
  have hfloor_lt : (fourthLog n) < (degreeCut n : ℝ) + 1 := by
    unfold degreeCut
    exact Nat.lt_floor_add_one _
  have hfloor_le : (degreeCut n : ℝ) ≤ fourthLog n := by
    unfold degreeCut
    exact Nat.floor_le (le_of_lt htpos)
  have hdivlow : 2 * descentCut n ≤ degreeCut n := by
    simp [ThresholdFoundations.descentCut]
    exact Nat.mul_div_le _ _
  have hdivhigh : degreeCut n ≤ 2 * descentCut n + 1 := by
    have hmod := Nat.mod_add_div (degreeCut n) 2
    have hmodlt := Nat.mod_lt (degreeCut n) (by norm_num : 0 < 2)
    simp [ThresholdFoundations.descentCut] at hmod ⊢
    omega
  have hwlt : descentCut n < degreeCut n := by
    unfold ThresholdFoundations.descentCut
    omega
  have hwlower : fourthLog n / 2 - 1 ≤ (descentCut n : ℝ) := by
    have hdivhighR : (degreeCut n : ℝ) ≤ 2 * (descentCut n : ℝ) + 1 := by
      exact_mod_cast hdivhigh
    have hfloor_ltR : fourthLog n < (degreeCut n : ℝ) + 1 := hfloor_lt
    exact (by linarith : fourthLog n / 2 - 1 ≤ (descentCut n : ℝ))
  have hgap : fourthLog n / 2 ≤ ((degreeCut n + 1 - descentCut n : ℕ) : ℝ) := by
    have hdivlowR : 2 * (descentCut n : ℝ) ≤ (degreeCut n : ℝ) := by
      exact_mod_cast hdivlow
    have hdivhighR : (degreeCut n : ℝ) ≤ 2 * (descentCut n : ℝ) + 1 := by
      exact_mod_cast hdivhigh
    have hgapNat : descentCut n + 1 ≤ degreeCut n + 1 - descentCut n := by omega
    have hgapR : (descentCut n : ℝ) + 1 ≤ (degreeCut n + 1 - descentCut n : ℕ) := by
      exact_mod_cast hgapNat
    linarith
  have hratio : 0 < (n : ℝ) / ((n : ℝ) - 1) := by positivity
  have hratio_le : (n : ℝ) / ((n : ℝ) - 1) ≤ 3 / 2 := by
    rw [div_le_iff₀ hnsub]
    nlinarith
  have hratio_sq : ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 ≤ 9 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio_le)
      (show 0 ≤ (3 / 2 : ℝ) + (n : ℝ) / ((n : ℝ) - 1) from by positivity)]
  have hKpos : 1 ≤ pivotalCut Λ := by
    unfold ThresholdFoundations.pivotalCut
    exact_mod_cast (Nat.ceil_pos.mpr (by positivity : 0 < (8 : ℝ) * Λ))
  have hKge : 8 * Λ ≤ (pivotalCut Λ : ℝ) := by
    unfold ThresholdFoundations.pivotalCut
    exact Nat.le_ceil _
  have hcap : (cap Λ n : ℝ) ≤ Λ * n := by
    unfold ThresholdFoundations.cap
    exact Nat.floor_le (by positivity)
  have hcontract : ∀ m : ℕ, m ≤ cap Λ n →
      2 * (m : ℝ) / ((n : ℝ) * pivotalCut Λ) ≤ 1 / 4 := by
    intro m hm
    have hmNatR : (m : ℝ) ≤ (cap Λ n : ℝ) := by exact_mod_cast hm
    have hmR : (m : ℝ) ≤ Λ * n := hmNatR.trans hcap
    have hden : 0 < (n : ℝ) * pivotalCut Λ := by positivity
    rw [div_le_iff₀ hden]
    have hKmul : (n : ℝ) * (8 * Λ) ≤ (n : ℝ) * (pivotalCut Λ : ℝ) :=
      mul_le_mul_of_nonneg_left hKge hnpos.le
    push_cast
    nlinarith
  have hwpos : pivotalCut Λ ≤ descentCut n → 1 ≤ descentCut n := by
    intro h
    exact le_trans hKpos h
  have hdenom : pivotalCut Λ ≤ descentCut n →
      2 ≤ descentCut n - pivotalCut Λ + 2 := by
    intro h
    omega
  exact {
    cap_le := hcap
    Kpos := hKpos
    Kge := hKge
    Dpos := hDpos
    div_lower := hdivlow
    div_upper := hdivhigh
    wlt := hwlt
    D_lower := by linarith
    w_lower := hwlower
    gap_lower := hgap
    root_pos := htpos
    root_pow := hroot
    ratio_pos := hratio
    ratio_sq := hratio_sq
    contraction := hcontract
    wpos := hwpos
    denom := hdenom
  }

end ThLean.W.S637

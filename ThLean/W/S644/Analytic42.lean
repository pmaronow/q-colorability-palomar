module

public import ThLean.BP.S6.Analytic

@[expose] public section

noncomputable section
open ThresholdFoundations

namespace ThLean.W.S644

theorem S6_42Statement_of_deps (h33 : ThLean.BP.S6.S6_33Statement) :
    ThLean.BP.S6.S6_42Statement := by
  intro n Λ hn hΛ hw hmajor
  have hp := h33 n Λ hn hΛ
  let t : ℝ := ThLean.BP.S6.fourthLog n
  let w : ℕ := descentCut n
  let K : ℕ := pivotalCut Λ
  let g : ℕ := degreeCut n + 1 - descentCut n
  let d : ℝ := (descentCut n - pivotalCut Λ + 2 : ℕ)
  have ht4 : t ^ 4 = Real.log (n : ℝ) := by
    simpa [t] using hp.root_pow
  have hgap : t ≤ 2 * (g : ℝ) := by
    have h := hp.gap_lower
    change ThLean.BP.S6.fourthLog n / 2 ≤ (g : ℝ) at h
    dsimp [t]
    nlinarith
  have hwlo : t / 2 - 1 ≤ (w : ℝ) := by
    simpa [t, w] using hp.w_lower
  have hdenomN : 2 ≤ descentCut n - pivotalCut Λ + 2 := hp.denom hw
  have hdenom : 2 ≤ d := by
    dsimp [d]
    exact_mod_cast hdenomN
  have hdpos : 0 < d := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2nn : 0 ≤ Real.log 2 := le_of_lt hlog2
  have hα : ThLean.BP.S6.alpha = Real.exp (-2 * Real.log 2) := by
    rw [ThLean.BP.S6.alpha]
    calc
      (1 : ℝ) / 4 = (Real.exp (Real.log 2 + Real.log 2))⁻¹ := by
        simp [Real.exp_add, Real.exp_log (by norm_num : 0 < (2 : ℝ))]; norm_num
      _ = Real.exp (-(Real.log 2 + Real.log 2)) := by rw [← Real.exp_neg]
      _ = Real.exp (-2 * Real.log 2) := by congr 1; ring
  have hpow (k : ℕ) : ThLean.BP.S6.alpha ^ k =
      Real.exp (-(Real.log 2) * (2 * (k : ℝ))) := by
    calc
      ThLean.BP.S6.alpha ^ k = (Real.exp (-2 * Real.log 2)) ^ k := by rw [hα]
      _ = Real.exp ((k : ℝ) * (-2 * Real.log 2)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (-(Real.log 2) * (2 * (k : ℝ))) := by congr 1; ring
  have hgapArg : -(Real.log 2) * (2 * (g : ℝ)) ≤ -(Real.log 2) * t :=
    mul_le_mul_of_nonpos_left hgap (neg_nonpos.mpr hlog2nn)
  have hzpow : (4 : ℝ) ^ (-(g : ℤ)) = ThLean.BP.S6.alpha ^ g := by
    simp [ThLean.BP.S6.alpha, zpow_neg, zpow_natCast, inv_pow]
  have hfirst : (4 : ℝ) ^ (-(g : ℤ)) ≤ Real.exp (-(Real.log 2) * t) := by
    rw [hzpow, hpow]
    exact Real.exp_le_exp.mpr hgapArg

  have hwposN : 0 < w := by
    have hK := hp.Kpos
    dsimp [w, K] at *
    omega
  have hwpos : 0 < (w : ℝ) := by exact_mod_cast hwposN
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hmainR : 2 * Real.exp 1 ^ 2 * Λ ≤ (w : ℝ) := by
    exact_mod_cast hmajor
  have hscaled := mul_le_mul_of_nonneg_right hmainR (inv_nonneg.mpr (le_of_lt hepos))
  have hnum : 2 * Real.exp 1 * Λ ≤ (w : ℝ) / Real.exp 1 := by
    calc
      2 * Real.exp 1 * Λ = (2 * Real.exp 1 ^ 2 * Λ) * (Real.exp 1)⁻¹ := by
        field_simp
      _ ≤ (w : ℝ) * (Real.exp 1)⁻¹ := hscaled
      _ = (w : ℝ) / Real.exp 1 := by rw [div_eq_mul_inv]
  have hbase : 2 * Real.exp 1 * Λ / (w : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    apply (div_le_iff₀ hwpos).2
    calc
      2 * Real.exp 1 * Λ ≤ (w : ℝ) / Real.exp 1 := hnum
      _ = (Real.exp 1)⁻¹ * (w : ℝ) := by ring
  have hbaseNN : 0 ≤ 2 * Real.exp 1 * Λ / (w : ℝ) := by positivity
  have hpowBase : (2 * Real.exp 1 * Λ / (w : ℝ)) ^ w ≤ Real.exp (-(w : ℝ)) := by
    calc
      (2 * Real.exp 1 * Λ / (w : ℝ)) ^ w ≤ (Real.exp (-1)) ^ w :=
        pow_le_pow_left₀ hbaseNN hbase w
      _ = Real.exp (-(w : ℝ)) := by
        calc
          (Real.exp (-1)) ^ w = Real.exp ((w : ℝ) * (-1)) := (Real.exp_nat_mul (-1) w).symm
          _ = Real.exp (-(w : ℝ)) := by congr 1; ring
  have hdecayArg : -(w : ℝ) ≤ 1 - t / 2 := by nlinarith [hwlo]
  have hdecay : Real.exp (-(w : ℝ)) ≤ Real.exp 1 * Real.exp (-t / 2) := by
    calc
      Real.exp (-(w : ℝ)) ≤ Real.exp (1 - t / 2) := Real.exp_le_exp.mpr hdecayArg
      _ = Real.exp 1 * Real.exp (-t / 2) := by
        rw [show 1 - t / 2 = 1 + -(t / 2) by ring, Real.exp_add]
        ring_nf

  have hlognn : 0 ≤ Real.log (n : ℝ) := by rw [← ht4]; positivity
  have hfrac' : t ^ 4 / d ≤ t ^ 4 / 2 := by
    apply (div_le_iff₀ hdpos).2
    calc
      t ^ 4 = t ^ 4 * 1 := by ring
      _ ≤ t ^ 4 * (d / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ = (t ^ 4 / 2) * d := by ring
  have hfrac : Real.log (n : ℝ) / d ≤ t ^ 4 / 2 := by
    rw [← ht4]
    exact hfrac'
  have hfracNN : 0 ≤ Real.log (n : ℝ) / d := div_nonneg hlognn hdpos.le
  have hratio := hp.ratio_sq
  have hcoefNN : 0 ≤ 32 * Λ / (3 * Real.log 2) := by positivity
  have hsecond :
      (32 * Λ / (3 * Real.log 2)) * ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 *
        (Real.log (n : ℝ) / d) * (2 * Real.exp 1 * Λ / (w : ℝ)) ^ w ≤
      (12 * Real.exp 1 * Λ / Real.log 2) * t ^ 4 * Real.exp (-t / 2) := by
    calc
      (32 * Λ / (3 * Real.log 2)) * ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 *
          (Real.log (n : ℝ) / d) * (2 * Real.exp 1 * Λ / (w : ℝ)) ^ w ≤
        (32 * Λ / (3 * Real.log 2)) * (9 / 4) * (t ^ 4 / 2) *
          (2 * Real.exp 1 * Λ / (w : ℝ)) ^ w := by
            calc
              _ ≤ (32 * Λ / (3 * Real.log 2)) * (9 / 4) *
                    (Real.log (n : ℝ) / d) * (2 * Real.exp 1 * Λ / (w : ℝ)) ^ w := by
                  apply mul_le_mul_of_nonneg_right
                  · apply mul_le_mul_of_nonneg_right
                    · exact mul_le_mul_of_nonneg_left hratio hcoefNN
                    · exact hfracNN
                  · exact pow_nonneg hbaseNN w
              _ ≤ _ := by
                  apply mul_le_mul_of_nonneg_right
                  · exact mul_le_mul_of_nonneg_left hfrac (by positivity)
                  · exact pow_nonneg hbaseNN w
      _ ≤ (32 * Λ / (3 * Real.log 2)) * (9 / 4) * (t ^ 4 / 2) *
          Real.exp (-(w : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hpowBase (by positivity)
      _ ≤ (32 * Λ / (3 * Real.log 2)) * (9 / 4) * (t ^ 4 / 2) *
          (Real.exp 1 * Real.exp (-t / 2)) := by
            exact mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = (12 * Real.exp 1 * Λ / Real.log 2) * t ^ 4 * Real.exp (-t / 2) := by
            field_simp [ne_of_gt hlog2]
            ring

  unfold highBound
  change (8 / 3 : ℝ) * (4 : ℝ) ^ (-(g : ℤ)) +
      (32 * Λ / (3 * Real.log 2)) * ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 *
        (Real.log (n : ℝ) / d) * (2 * Real.exp 1 * Λ / (w : ℝ)) ^ w ≤ _
  exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num)) hsecond

end ThLean.W.S644

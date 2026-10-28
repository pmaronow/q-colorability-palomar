import ThLean.BP.SA.Quantiles
import ThLean.BP.SA.Common

noncomputable section

open Filter
open scoped Topology

namespace ThLean.W.SA44

open ThresholdFoundations ThLean.BP.SA

theorem SA_Q23bStatement_holds : ThLean.BP.SA.SA_Q23bStatement := by
  constructor
  · intro n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    let x : ℝ := Real.sqrt (n : ℝ) * Real.log (n : ℝ)
    have hx0 : 0 ≤ x := by
      dsimp [x]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
    constructor
    · unfold poissonDeviation
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · have hceil : (Nat.ceil x : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0).le
      have hsqrt : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
      have hratio : x / (n : ℝ) = Real.log (n : ℝ) / Real.sqrt (n : ℝ) := by
        calc
          x / (n : ℝ) =
              (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) /
                (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by
                  dsimp [x]
                  rw [hsqrt]
          _ = Real.log (n : ℝ) / Real.sqrt (n : ℝ) := by
                field_simp [ne_of_gt (Real.sqrt_pos.2 hn0)]
      have hdiv := div_le_div_of_nonneg_right hceil (Nat.cast_nonneg n)
      unfold poissonDeviation envelope
      calc
        (Nat.ceil (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) : ℝ) / (n : ℝ)
            ≤ (Real.sqrt (n : ℝ) * Real.log (n : ℝ) + 1) / (n : ℝ) := by
              simpa [x] using hdiv
        _ = Real.log (n : ℝ) / Real.sqrt (n : ℝ) + 1 / (n : ℝ) := by
              rw [add_div, hratio]
  · intro Λ hΛ
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp hnat
    have hexp : Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ))) atTop (𝓝 0) := by
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlog)
    have hupper : ∀ᶠ n : ℕ in atTop,
        poissonTailError Λ n ≤ Real.exp (-Real.log (n : ℝ)) := by
      filter_upwards [hlog.eventually_ge_atTop (2 * Λ)] with n hn
      have hx0 : 0 ≤ Real.log (n : ℝ) := by linarith
      have hxmul := mul_nonneg (sub_nonneg.mpr hn) hx0
      have hxdiv : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 / (2 * Λ) := by
        apply (le_div_iff₀ (by positivity : 0 < 2 * Λ)).2
        nlinarith [hxmul]
      have hexp_le : Real.exp (-((Real.log (n : ℝ)) ^ 2) / (2 * Λ)) ≤
          Real.exp (-Real.log (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        exact neg_le_neg hxdiv
      simpa [poissonTailError] using hexp_le
    have hlower : ∀ᶠ n : ℕ in atTop, 0 ≤ poissonTailError Λ n :=
      Eventually.of_forall (fun n => le_of_lt (Real.exp_pos _))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      hlower hupper

end ThLean.W.SA44

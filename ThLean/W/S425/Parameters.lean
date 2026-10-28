import ThLean.BP.S4.Parameters

noncomputable section

namespace ThLean.W.S425

open ThresholdFoundations

theorem S4_PAR_01AStatement_holds : ThLean.BP.S4.S4_PAR_01AStatement := by
  intro q hq
  have hq_real : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast (show 1 < q by omega)
  have hq_sub : 0 < (q : ℝ) - 1 := by
    linarith
  have hratio : 1 < (q : ℝ) / ((q : ℝ) - 1) := by
    rw [lt_div_iff₀ hq_sub]
    nlinarith
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq_real
  have hlogratio : 0 < Real.log ((q : ℝ) / ((q : ℝ) - 1)) :=
    Real.log_pos hratio
  have hgamma : 0 < gamma q := by
    unfold gamma
    exact div_pos hlogq hlogratio
  refine ⟨hlogq, hlogratio, hgamma, ?_⟩
  intro Λ hΛ
  have hΛ_one : 1 < Λ := by
    linarith
  have heta_pos : 0 < etaZero Λ := by
    unfold etaZero
    positivity
  have hexp_lt_one : Real.exp (-2 * Λ) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have heta_lt_half : etaZero Λ < 1 / 2 := by
    unfold etaZero
    have hdiv : Real.exp (-2 * Λ) / 8 < (1 : ℝ) / 8 :=
      div_lt_div_of_pos_right hexp_lt_one (by norm_num)
    norm_num at hdiv ⊢
    linarith
  refine ⟨hΛ_one, heta_pos, heta_lt_half, ?_, ?_⟩
  · intro η hη hηle
    have hη_lt_half : η < 1 / 2 := lt_of_le_of_lt hηle heta_lt_half
    have hη_sq_pos : 0 < η ^ 2 := sq_pos_of_pos hη
    have hη_sq_lt_one : η ^ 2 < 1 := by nlinarith
    constructor
    · rw [le_div_iff₀ hη_sq_pos]
      nlinarith
    · exact div_pos (by nlinarith) hη_sq_pos
  · intro n
    have hfloor : (Nat.floor (Λ * (n : ℝ)) : ℝ) ≤ Λ * (n : ℝ) :=
      Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg n))
    simpa [cap] using hfloor

example : ThLean.BP.S4.S4_PAR_01AStatement :=
  S4_PAR_01AStatement_holds

end ThLean.W.S425

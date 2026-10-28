import ThLean.BP.S3.Centre

noncomputable section

namespace ThLean.W.S375

open ThresholdFoundations

private theorem ratioLog_pos (q : ℕ) (hq : 2 ≤ q) :
    0 < Real.log ((q : ℝ) / ((q : ℝ) - 1)) ∧ 0 < Real.log (q : ℝ) := by
  have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) - 1 := by linarith
  have hratio : 1 < (q : ℝ) / ((q : ℝ) - 1) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  exact ⟨Real.log_pos hratio, Real.log_pos (by linarith)⟩

private theorem gamma_ge_one (q : ℕ) (hq : 2 ≤ q) : 1 ≤ gamma q := by
  have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) - 1 := by linarith
  have hratio : 1 < (q : ℝ) / ((q : ℝ) - 1) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  have hlogden : 0 < Real.log ((q : ℝ) / ((q : ℝ) - 1)) := Real.log_pos hratio
  have hquot : (q : ℝ) / ((q : ℝ) - 1) ≤ (q : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hlogle := Real.log_le_log (div_pos (by linarith) hden) hquot
  unfold gamma
  exact (le_div_iff₀ hlogden).2 (by simpa using hlogle)

private theorem rounded_survival_bound
    (h24 : ThLean.BP.S3.S3_24Statement.{0})
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (n : ℕ)
    (hβ : gamma q < β) (hn : 2*q ≤ n) :
    processSurvival (V := Fin n) q (Nat.floor (β*n)) ≤
      (((q : ℝ) / ((q : ℝ)-1)) * Real.exp (2*β)) *
        Real.exp (-(n : ℝ)*(β-gamma q)*Real.log ((q : ℝ)/((q : ℝ)-1))) := by
  let k : ℕ := Nat.floor (β*n)
  let a : ℝ := Real.log ((q : ℝ) / ((q : ℝ)-1))
  let X : ℝ := (q : ℝ)^n *
    ((((q : ℝ)-1)/(q : ℝ)) * ((n : ℝ)/((n : ℝ)-1)))^k
  have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hnNat : 2 ≤ n := by omega
  have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hnNat
  have hdenq : 0 < (q : ℝ)-1 := by linarith
  have hdenn : 0 < (n : ℝ)-1 := by linarith
  have hratio_pos : 0 < (q : ℝ)/((q : ℝ)-1) := div_pos (by linarith) hdenq
  have ha : 0 < a := by
    dsimp [a]
    exact Real.log_pos (by
      rw [lt_div_iff₀ hdenq]
      nlinarith)
  have hbeta_pos : 0 < β := (lt_of_lt_of_le zero_lt_one (gamma_ge_one q hq)).trans hβ
  have hfloor_le : (k : ℝ) ≤ β*n := by
    dsimp [k]
    exact Nat.floor_le (by positivity)
  have hfloor_gt : β*n - 1 < (k : ℝ) := by
    dsimp [k]
    have hf : β*n < (Nat.floor (β*n) : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hncard : 2 ≤ Fintype.card (Fin n) := by simpa using hnNat
  have h24bound := h24 (Fin n) q hq hncard (0 : MGraph (Fin n)) k
  have hsX : processSurvival (V := Fin n) q k ≤ X := by
    simpa [processSurvival, X, k] using h24bound.1
  have hratio_inv : ((q : ℝ)-1)/(q : ℝ) = ((q : ℝ)/((q : ℝ)-1))⁻¹ := by
    field_simp
  have hlog_left : Real.log (((q : ℝ)-1)/(q : ℝ)) = -a := by
    rw [hratio_inv, Real.log_inv]
  have hnratio_pos : 0 < (n : ℝ)/((n : ℝ)-1) := div_pos (by linarith) hdenn
  have hlog_right : Real.log ((n : ℝ)/((n : ℝ)-1)) ≤ 1/((n : ℝ)-1) := by
    have ht := Real.log_le_sub_one_of_pos hnratio_pos
    have heq : (n : ℝ)/((n : ℝ)-1) - 1 = 1/((n : ℝ)-1) := by
      field_simp
      ring
    rw [heq] at ht
    exact ht
  have hlogX : Real.log X = (n : ℝ)*Real.log (q : ℝ) +
      (k : ℝ) * (Real.log (((q : ℝ)-1)/(q : ℝ)) +
        Real.log ((n : ℝ)/((n : ℝ)-1))) := by
    dsimp [X]
    rw [Real.log_mul (pow_ne_zero _ (by positivity))
        (pow_ne_zero _ (by positivity)), Real.log_pow, Real.log_pow,
        Real.log_mul (by positivity) (by positivity)]
  have hlog_factor :
      Real.log (((q : ℝ)-1)/(q : ℝ)) + Real.log ((n : ℝ)/((n : ℝ)-1)) ≤
        -a + 1/((n : ℝ)-1) := by
    rw [hlog_left]
    linarith
  have hfrac : (n : ℝ)/((n : ℝ)-1) ≤ 2 := by
    rw [div_le_iff₀ hdenn]
    nlinarith
  have hfloor_tail : (k : ℝ)/((n : ℝ)-1) ≤ 2*β := by
    calc
      (k : ℝ)/((n : ℝ)-1) ≤ (β*n)/((n : ℝ)-1) :=
        div_le_div_of_nonneg_right hfloor_le hdenn.le
      _ = β * ((n : ℝ)/((n : ℝ)-1)) := by ring
      _ ≤ β*2 := mul_le_mul_of_nonneg_left hfrac hbeta_pos.le
      _ = 2*β := by ring
  have hfloor_exponent : (β*n-1)*a ≤ (k : ℝ)*a :=
    mul_le_mul_of_nonneg_right (le_of_lt hfloor_gt) ha.le
  have hgamma : gamma q * a = Real.log (q : ℝ) := by
    dsimp [gamma, a]
    exact div_mul_cancel₀ _ (ne_of_gt ha)
  have hlog_bound : Real.log X ≤
      -(n : ℝ)*(β-gamma q)*a + a + 2*β := by
    rw [hlogX]
    have hmul := mul_le_mul_of_nonneg_left hlog_factor (Nat.cast_nonneg k)
    have hstep : (n : ℝ)*Real.log (q : ℝ) +
        (k : ℝ) * (Real.log (((q : ℝ)-1)/(q : ℝ)) +
          Real.log ((n : ℝ)/((n : ℝ)-1))) ≤
        (n : ℝ)*Real.log (q : ℝ) - (k : ℝ)*a + (k : ℝ)/((n : ℝ)-1) := by
      calc
        (n : ℝ)*Real.log (q : ℝ) +
            (k : ℝ) * (Real.log (((q : ℝ)-1)/(q : ℝ)) +
              Real.log ((n : ℝ)/((n : ℝ)-1))) ≤
            (n : ℝ)*Real.log (q : ℝ) + (k : ℝ) * (-a + 1/((n : ℝ)-1)) :=
          by linarith [hmul]
        _ = (n : ℝ)*Real.log (q : ℝ) - (k : ℝ)*a + (k : ℝ)/((n : ℝ)-1) := by ring
    calc
      (n : ℝ)*Real.log (q : ℝ) +
          (k : ℝ) * (Real.log (((q : ℝ)-1)/(q : ℝ)) +
            Real.log ((n : ℝ)/((n : ℝ)-1))) ≤
          (n : ℝ)*Real.log (q : ℝ) - (k : ℝ)*a + (k : ℝ)/((n : ℝ)-1) := hstep
      _ ≤ (n : ℝ)*Real.log (q : ℝ) - (β*n-1)*a + 2*β := by
        nlinarith [hfloor_tail, hfloor_exponent]
      _ = -(n : ℝ)*(β-gamma q)*a + a + 2*β := by
        rw [← hgamma]
        ring
  have hXpos : 0 < X := by
    dsimp [X]
    positivity
  have hXexp : X ≤ Real.exp (-(n : ℝ)*(β-gamma q)*a + a + 2*β) := by
    calc
      X = Real.exp (Real.log X) := (Real.exp_log hXpos).symm
      _ ≤ Real.exp (-(n : ℝ)*(β-gamma q)*a + a + 2*β) :=
        Real.exp_le_exp.mpr hlog_bound
  have hfinal : Real.exp (-(n : ℝ)*(β-gamma q)*a + a + 2*β) =
      (((q : ℝ)/((q : ℝ)-1))*Real.exp (2*β)) *
        Real.exp (-(n : ℝ)*(β-gamma q)*a) := by
    rw [show -(n : ℝ)*(β-gamma q)*a + a + 2*β =
      a + 2*β + (-(n : ℝ)*(β-gamma q)*a) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log hratio_pos]
  rw [show Nat.floor (β*n) = k by rfl]
  calc
    processSurvival (V := Fin n) q k ≤ X := hsX
    _ ≤ Real.exp (-(n : ℝ)*(β-gamma q)*a + a + 2*β) := hXexp
    _ = (((q : ℝ)/((q : ℝ)-1))*Real.exp (2*β)) *
          Real.exp (-(n : ℝ)*(β-gamma q)*a) := hfinal

theorem S3_52Statement_of_deps (h24 : ThLean.BP.S3.S3_24Statement.{0}) :
    ThLean.BP.S3.S3_52Statement := by
  intro q hq
  refine ⟨(ratioLog_pos q hq).1, (ratioLog_pos q hq).2, gamma_ge_one q hq, ?_, ?_⟩
  · intro β n hβ hn
    exact rounded_survival_bound h24 q hq β n hβ hn
  · intro Λ hΛ
    have hΛ2 : 2 < Λ := by linarith [gamma_ge_one q hq]
    refine ⟨hΛ2, ?_, ?_⟩
    · unfold etaZero
      positivity
    · unfold etaZero
      have hexp : Real.exp (-2*Λ) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith
      calc
        Real.exp (-2*Λ)/8 < (1 : ℝ)/8 := div_lt_div_of_pos_right hexp (by norm_num)
        _ < 1/2 := by norm_num

end ThLean.W.S375

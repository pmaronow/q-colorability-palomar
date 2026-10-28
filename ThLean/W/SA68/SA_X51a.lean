import ThLean.BP.SA.Transfer

noncomputable section
open scoped BigOperators

namespace ThLean.W.SA68

private lemma exp_neg_quad_le_one_sub (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-(x + 2 * x ^ 2)) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by linarith
  have hratio : x / (1 - x) ≤ x + 2 * x ^ 2 := by
    rw [div_le_iff₀ hpos]
    have haux : 0 ≤ x ^ 2 * (1 - 2 * x) :=
      mul_nonneg (sq_nonneg x) (by linarith)
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  have hlog' : -(x + 2 * x ^ 2) ≤ Real.log (1 - x) := by
    have hinv : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
    rw [hinv] at hlog
    linarith
  have hexp := Real.exp_le_exp.mpr hlog'
  rw [Real.exp_log hpos] at hexp
  exact hexp

private lemma choose_two_cast (n : ℕ) (hn : 2 ≤ n) :
    (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rw [Nat.choose_two_right,
    Nat.cast_div (Nat.even_mul_pred_self n).two_dvd (by norm_num : (2 : ℝ) ≠ 0),
    Nat.cast_mul, Nat.cast_sub (by omega)]
  ring

/-- The finite birthday estimate, using the exact product formula from X50b. -/
theorem SA_X51aStatement_of_deps
    (h50 : ThLean.BP.SA.SA_X50bStatement) :
    ThLean.BP.SA.SA_X51aStatement := by
  intro Λ n hΛ hn hlinear hcubic m hm
  let N : ℝ := n
  let B : ℝ := n.choose 2
  have hN : 2 ≤ N := by dsimp [N]; exact_mod_cast hn
  have hNm1 : 0 < N - 1 := by linarith
  have hB : B = N * (N - 1) / 2 := by
    dsimp [B, N]
    exact choose_two_cast n hn
  have hBpos : 0 < B := by rw [hB]; positivity
  have hΛN : 0 ≤ Λ * N := mul_nonneg hΛ (by positivity)
  have hmR : (m : ℝ) ≤ Λ * N := by simpa [N] using hm
  have hfourN : 4 * Λ * N ≤ N * (N - 1) := by
    have := mul_le_mul_of_nonneg_right hlinear (by positivity : 0 ≤ N)
    nlinarith
  have hmB : (m : ℝ) ≤ B := by
    rw [hB]
    nlinarith
  have hmvalid : m ≤ n.choose 2 := by
    have hmB' : (m : ℝ) ≤ (n.choose 2 : ℝ) := by simpa [B] using hmB
    exact_mod_cast hmB'
  refine ⟨hmvalid, ?_⟩
  obtain ⟨hprob, _hpos⟩ := h50 n m hn hmvalid
  rw [hprob]
  let x (i : ℕ) : ℝ := (i : ℝ) / B
  let S₁ : ℝ := ∑ i ∈ Finset.range m, x i
  let S₂ : ℝ := ∑ i ∈ Finset.range m, (x i) ^ 2
  have hsumI : (∑ i ∈ Finset.range m, (i : ℝ)) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hmpos : 1 ≤ m := Nat.pos_of_ne_zero hm0
      rw [← Nat.cast_sum, Finset.sum_range_id,
        Nat.cast_div (Nat.even_mul_pred_self m).two_dvd (by norm_num : (2 : ℝ) ≠ 0),
        Nat.cast_mul, Nat.cast_sub hmpos]
      norm_num
  have hS₁eq : S₁ = ((m : ℝ) * ((m : ℝ) - 1) / 2) / B := by
    dsimp [S₁, x]
    rw [← Finset.sum_div, hsumI]
  have hS₁ : S₁ ≤ 2 * Λ ^ 2 := by
    rw [hS₁eq]
    have hden : 0 < 2 * B := by positivity
    have hratio : N / (N - 1) ≤ 2 := by
      apply (div_le_iff₀ hNm1).2
      nlinarith
    have hnum : (m : ℝ) * ((m : ℝ) - 1) ≤ (m : ℝ) ^ 2 := by
      have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    calc
      ((m : ℝ) * ((m : ℝ) - 1) / 2) / B ≤ (m : ℝ) ^ 2 / (2 * B) := by
        rw [div_div]
        exact div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (Λ * N) ^ 2 / (2 * B) := by
        apply div_le_div_of_nonneg_right _ hden.le
        have hsq : 0 ≤ (Λ * N - (m : ℝ)) * (Λ * N + (m : ℝ)) :=
          mul_nonneg (sub_nonneg.mpr hmR) (by positivity)
        nlinarith
      _ = Λ ^ 2 * (N / (N - 1)) := by rw [hB]; field_simp
      _ ≤ 2 * Λ ^ 2 := by
        have hΛsq : 0 ≤ Λ ^ 2 := sq_nonneg Λ
        nlinarith
  have hS₂bound : S₂ ≤ (m : ℝ) ^ 3 / (2 * B ^ 2) := by
    dsimp [S₂, x]
    calc
      (∑ i ∈ Finset.range m, ((i : ℝ) / B) ^ 2) ≤
          ∑ i ∈ Finset.range m, ((m : ℝ) * (i : ℝ)) / B ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hiNat : i ≤ m := Nat.le_of_lt (Finset.mem_range.mp hi)
        have hiR : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
        have hiLe : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hiNat
        rw [div_pow]
        apply div_le_div_of_nonneg_right _ (sq_nonneg B)
        nlinarith [mul_le_mul_of_nonneg_right hiLe hiR]
      _ = ((m : ℝ) * (∑ i ∈ Finset.range m, (i : ℝ))) / B ^ 2 := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
      _ = ((m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1) / 2)) / B ^ 2 := by rw [hsumI]
      _ ≤ (m : ℝ) ^ 3 / (2 * B ^ 2) := by
        have hnum : (m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1) / 2) ≤ (m : ℝ) ^ 3 / 2 := by
          have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
          nlinarith
        calc
          ((m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1) / 2)) / B ^ 2 ≤
              ((m : ℝ) ^ 3 / 2) / B ^ 2 :=
            div_le_div_of_nonneg_right hnum (sq_nonneg B)
          _ = (m : ℝ) ^ 3 / (2 * B ^ 2) := by field_simp
  have hmSq : (m : ℝ) ^ 2 ≤ (Λ * N) ^ 2 := by
    have haux : 0 ≤ (Λ * N - (m : ℝ)) * (Λ * N + (m : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hmR) (by positivity)
    nlinarith
  have hmCube : (m : ℝ) ^ 3 ≤ (Λ * N) ^ 3 := by
    calc
      (m : ℝ) ^ 3 = (m : ℝ) ^ 2 * (m : ℝ) := by ring
      _ ≤ (Λ * N) ^ 2 * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hmSq (Nat.cast_nonneg m)
      _ ≤ (Λ * N) ^ 2 * (Λ * N) :=
        mul_le_mul_of_nonneg_left hmR (sq_nonneg (Λ * N))
      _ = (Λ * N) ^ 3 := by ring
  have hmcubeB : (m : ℝ) ^ 3 / B ^ 2 ≤ 1 := by
    calc
      (m : ℝ) ^ 3 / B ^ 2 ≤ (Λ * N) ^ 3 / B ^ 2 :=
        div_le_div_of_nonneg_right hmCube (sq_nonneg B)
      _ = 4 * Λ ^ 3 * N / (N - 1) ^ 2 := by rw [hB]; field_simp; ring
      _ ≤ 1 := by exact hcubic
  have hmcube : (m : ℝ) ^ 3 ≤ B ^ 2 :=
    by
      have hmcube' : (m : ℝ) ^ 3 ≤ 1 * B ^ 2 :=
        (div_le_iff₀ (by positivity : 0 < B ^ 2)).1 hmcubeB
      nlinarith
  have hS₂ : 2 * S₂ ≤ 1 := by
    have hS₂' : S₂ ≤ 1 / 2 := by
      calc
        S₂ ≤ (m : ℝ) ^ 3 / (2 * B ^ 2) := hS₂bound
        _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity : 0 < 2 * B ^ 2)]
          nlinarith [hmcube]
    nlinarith
  have hx : ∀ i ∈ Finset.range m, 0 ≤ x i ∧ x i ≤ 1 / 2 := by
    intro i hi
    have hiNat : i ≤ m := Nat.le_of_lt (Finset.mem_range.mp hi)
    have hiR : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hiLe : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hiNat
    have hLambdaB : Λ * N ≤ B / 2 := by nlinarith [hfourN, hB]
    constructor
    · dsimp [x]
      positivity
    · dsimp [x]
      calc
        (i : ℝ) / B ≤ (m : ℝ) / B := div_le_div_of_nonneg_right hiLe hBpos.le
        _ ≤ (Λ * N) / B := div_le_div_of_nonneg_right hmR hBpos.le
        _ ≤ 1 / 2 := (div_le_iff₀ hBpos).2 (by linarith [hLambdaB])
  have hprod :
      (∏ i ∈ Finset.range m, Real.exp (-(x i + 2 * (x i) ^ 2))) ≤
        ∏ i ∈ Finset.range m, (1 - x i) := by
    apply Finset.prod_le_prod₀ (fun i hi => (Real.exp_pos _).le)
    intro i hi
    exact exp_neg_quad_le_one_sub (x i) (hx i hi).1 (hx i hi).2
  have hprodExp :
      (∏ i ∈ Finset.range m, Real.exp (-(x i + 2 * (x i) ^ 2))) =
        Real.exp (-(S₁ + 2 * S₂)) := by
    rw [← Real.exp_sum]
    dsimp [S₁, S₂, x]
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hExp : Real.exp (-2 * Λ ^ 2 - 1) ≤ Real.exp (-(S₁ + 2 * S₂)) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    Real.exp (-2 * Λ ^ 2 - 1) ≤ Real.exp (-(S₁ + 2 * S₂)) := hExp
    _ = ∏ i ∈ Finset.range m, Real.exp (-(x i + 2 * (x i) ^ 2)) := hprodExp.symm
    _ ≤ ∏ i ∈ Finset.range m, (1 - x i) := hprod

end ThLean.W.SA68

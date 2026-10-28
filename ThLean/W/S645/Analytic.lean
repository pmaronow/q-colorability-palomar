import ThLean.BP.S6.Analytic

noncomputable section

open ThresholdFoundations

namespace ThLean.W.S645

theorem S6_43Statement_of_deps
    (h33 : ThLean.BP.S6.S6_33Statement)
    (h42 : ThLean.BP.S6.S6_42Statement)
    (hx01 : ThLean.BP.S6.S6_X01Statement) :
    ThLean.BP.S6.S6_43Statement := by
  intro n Λ hn hΛ hcut
  let t : ℝ := ThLean.BP.S6.fourthLog n
  let l : ℝ := Real.log 2
  let k : ℝ := 2 * ((pivotalCut Λ : ℝ) + 1)
  let b : ℝ := 4 * Real.exp 1 ^ 2 * Λ + 2
  let c7 : ℝ := 16 * (Nat.factorial 7 : ℝ) / (3 * Real.log 2 ^ 7)
  let c11 : ℝ := 24 * Real.exp 1 * Λ * (2 : ℝ) ^ 11 *
    (Nat.factorial 11 : ℝ) / Real.log 2
  have hp : ThLean.BP.S6.ParameterFacts n Λ := h33 n Λ hn hΛ
  have htpos : 0 < t := by
    have h1 : 1 ≤ ThLean.BP.S6.analyticCutoff Λ := by
      unfold ThLean.BP.S6.analyticCutoff
      exact le_max_left _ _
    have h1t : 1 ≤ t := by
      dsimp [t]
      exact h1.trans hcut
    linarith
  have hlpos : 0 < l := by
    dsimp [l]
    exact Real.log_pos (by norm_num)
  have hKcut : 2 * ((pivotalCut Λ : ℝ) + 1) ≤ t := by
    have hK : 2 * ((pivotalCut Λ : ℝ) + 1) ≤ ThLean.BP.S6.analyticCutoff Λ := by
      unfold ThLean.BP.S6.analyticCutoff
      exact (le_max_left _ _).trans (le_max_right _ _)
    exact hK.trans hcut
  have hBcut : 4 * Real.exp 1 ^ 2 * Λ + 2 ≤ t := by
    have hB : 4 * Real.exp 1 ^ 2 * Λ + 2 ≤ ThLean.BP.S6.analyticCutoff Λ := by
      unfold ThLean.BP.S6.analyticCutoff
      exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    exact hB.trans hcut
  have h7cut : 16 * (Nat.factorial 7 : ℝ) / (3 * l ^ 7) ≤ t := by
    have hc : c7 ≤ ThLean.BP.S6.analyticCutoff Λ := by
      change c7 ≤ max 1 (max k (max b (max c7 c11)))
      have h0 : c7 ≤ max c7 c11 := le_max_left _ _
      have h1 : max c7 c11 ≤ max b (max c7 c11) := le_max_right _ _
      have h2 : max b (max c7 c11) ≤ max k (max b (max c7 c11)) := le_max_right _ _
      have h3 : max k (max b (max c7 c11)) ≤ max 1 (max k (max b (max c7 c11))) :=
        le_max_right _ _
      exact h0.trans (h1.trans (h2.trans h3))
    simpa [t, l, c7] using hc.trans hcut
  have h11cut :
      24 * Real.exp 1 * Λ * (2 : ℝ) ^ 11 * (Nat.factorial 11 : ℝ) / l ≤ t := by
    have hc : c11 ≤ ThLean.BP.S6.analyticCutoff Λ := by
      change c11 ≤ max 1 (max k (max b (max c7 c11)))
      have h0 : c11 ≤ max c7 c11 := le_max_right _ _
      have h1 : max c7 c11 ≤ max b (max c7 c11) := le_max_right _ _
      have h2 : max b (max c7 c11) ≤ max k (max b (max c7 c11)) := le_max_right _ _
      have h3 : max k (max b (max c7 c11)) ≤ max 1 (max k (max b (max c7 c11))) :=
        le_max_right _ _
      exact h0.trans (h1.trans (h2.trans h3))
    simpa [t, l, c11] using hc.trans hcut
  have hpiv : pivotalCut Λ ≤ descentCut n := by
    have hreal : (pivotalCut Λ : ℝ) ≤ t / 2 - 1 := by
      linarith
    have hreal' : (pivotalCut Λ : ℝ) ≤ (descentCut n : ℝ) := by
      exact hreal.trans (by simpa [t] using hp.w_lower)
    exact_mod_cast hreal'
  have hdescent : 2 * Real.exp 1 ^ 2 * Λ ≤ (descentCut n : ℝ) := by
    have hreal : 2 * Real.exp 1 ^ 2 * Λ ≤ t / 2 - 1 := by
      linarith
    exact hreal.trans (by simpa [t] using hp.w_lower)
  have htroot : t ^ 4 = Real.log (n : ℝ) := by
    simpa [t] using hp.root_pow
  have heps : epsilon n = Real.rpow t (-(6 : ℝ)) := by
    unfold epsilon
    rw [ite_eq_right (by omega)]
    rw [← htroot]
    calc
      Real.rpow (t ^ 4) (-(3 : ℝ) / 2) =
          Real.rpow (Real.rpow t (4 : ℝ)) (-(3 : ℝ) / 2) :=
        congrArg (fun x : ℝ => Real.rpow x (-(3 : ℝ) / 2))
          (Real.rpow_natCast t 4).symm
      _ = Real.rpow t ((4 : ℝ) * (-(3 : ℝ) / 2)) :=
        (Real.rpow_mul htpos.le (4 : ℝ) (-(3 : ℝ) / 2)).symm
      _ = Real.rpow t (-(6 : ℝ)) := by norm_num
  have hpow : Real.rpow t (-(6 : ℝ)) = 1 / t ^ 6 := by
    calc
      Real.rpow t (-(6 : ℝ)) = (Real.rpow t (6 : ℝ))⁻¹ :=
        Real.rpow_neg htpos.le 6
      _ = (t ^ 6)⁻¹ := congrArg Inv.inv (Real.rpow_natCast t 6)
      _ = 1 / t ^ 6 := by ring
  have h7exp : Real.exp (-(l * t)) ≤ (Nat.factorial 7 : ℝ) / (t * l) ^ 7 := by
    simpa [mul_comm] using hx01.2 (t * l) 7 (by positivity)
  have h7coef :
      (8 / 3 : ℝ) * (Nat.factorial 7 : ℝ) / l ^ 7 ≤ t / 2 := by
    have hscaled :
        (8 / 3 : ℝ) * (Nat.factorial 7 : ℝ) / l ^ 7 =
          (16 * (Nat.factorial 7 : ℝ) / (3 * l ^ 7)) / 2 := by
      field_simp
      ring
    rw [hscaled]
    exact div_le_div_of_nonneg_right h7cut (by norm_num)
  have hfirst :
      (8 / 3 : ℝ) * Real.exp (-(l * t)) ≤ 1 / (2 * t ^ 6) := by
    calc
      (8 / 3 : ℝ) * Real.exp (-(l * t)) ≤
          (8 / 3 : ℝ) * ((Nat.factorial 7 : ℝ) / (t * l) ^ 7) :=
        mul_le_mul_of_nonneg_left h7exp (by norm_num)
      _ = ((8 / 3 : ℝ) * (Nat.factorial 7 : ℝ) / l ^ 7) / t ^ 7 := by
        field_simp [ne_of_gt htpos, ne_of_gt hlpos]
      _ ≤ (t / 2) / t ^ 7 := div_le_div_of_nonneg_right h7coef (by positivity)
      _ = 1 / (2 * t ^ 6) := by
        field_simp [ne_of_gt htpos]
  have h11exp : Real.exp (-(t / 2)) ≤ (Nat.factorial 11 : ℝ) / (t / 2) ^ 11 := by
    exact hx01.2 (t / 2) 11 (by positivity)
  have h11coef :
      (12 * Real.exp 1 * Λ * (2 : ℝ) ^ 11 * (Nat.factorial 11 : ℝ) / l) ≤ t / 2 := by
    have hscaled :
        12 * Real.exp 1 * Λ * (2 : ℝ) ^ 11 * (Nat.factorial 11 : ℝ) / l =
          (24 * Real.exp 1 * Λ * (2 : ℝ) ^ 11 * (Nat.factorial 11 : ℝ) / l) / 2 := by
      ring
    rw [hscaled]
    exact div_le_div_of_nonneg_right h11cut (by norm_num)
  have hsecond :
      (12 * Real.exp 1 * Λ / l) * t ^ 4 * Real.exp (-(t / 2)) ≤
        1 / (2 * t ^ 6) := by
    calc
      (12 * Real.exp 1 * Λ / l) * t ^ 4 * Real.exp (-(t / 2)) ≤
          (12 * Real.exp 1 * Λ / l) * t ^ 4 *
            ((Nat.factorial 11 : ℝ) / (t / 2) ^ 11) := by
        apply mul_le_mul_of_nonneg_left h11exp
        positivity
      _ = (12 * Real.exp 1 * Λ * (2 : ℝ) ^ 11 *
            (Nat.factorial 11 : ℝ) / l) / t ^ 7 := by
        field_simp [ne_of_gt htpos, ne_of_gt hlpos]
      _ ≤ (t / 2) / t ^ 7 := div_le_div_of_nonneg_right h11coef (by positivity)
      _ = 1 / (2 * t ^ 6) := by
        field_simp [ne_of_gt htpos]
  have h42bound := h42 n Λ hn hΛ hpiv hdescent
  have hsum := add_le_add hfirst hsecond
  have hhigh : highBound Λ n ≤ 1 / (2 * t ^ 6) + 1 / (2 * t ^ 6) := by
    have h42' : highBound Λ n ≤
        (8 / 3 : ℝ) * Real.exp (-(l * t)) +
          (12 * Real.exp 1 * Λ / l) * t ^ 4 * Real.exp (-(t / 2)) := by
      simpa [t, l, neg_div] using h42bound
    exact h42'.trans hsum
  have hfinal : highBound Λ n ≤ epsilon n := by
    calc
      highBound Λ n ≤ 1 / (2 * t ^ 6) + 1 / (2 * t ^ 6) := hhigh
      _ = 1 / t ^ 6 := by field_simp [ne_of_gt htpos]; ring
      _ = epsilon n := by rw [← hpow, ← heps]
  exact ⟨hpiv, hdescent, hfinal⟩

end ThLean.W.S645

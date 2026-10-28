import ThLean.BP.SA.Transfer

noncomputable section

namespace ThLean.W.SA69

theorem SA_X51bStatement_holds : ThLean.BP.SA.SA_X51bStatement := by
  intro Λ hΛ
  let C : ℝ := max (4 * Λ + 1) (8 * Λ ^ 3 + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt C
  have hC : (1 : ℝ) ≤ C := by
    dsimp [C]
    exact le_trans (by nlinarith) (le_max_left _ _)
  have hNreal : C < (N : ℝ) := hN
  have hNatOne : 1 < N := by
    exact_mod_cast (lt_of_le_of_lt hC hNreal)
  have hNtwo : 2 ≤ N := by omega
  refine ⟨N, hNtwo, ?_⟩
  intro n hn
  have hnNatTwo : 2 ≤ n := le_trans hNtwo hn
  have hnReal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hFirstCut : 4 * Λ + 1 < (N : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hNreal
  have hSecondCut : 8 * Λ ^ 3 + 1 < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hNreal
  have hFirst : 4 * Λ ≤ (n : ℝ) - 1 := by
    linarith
  have hnRealTwo : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnNatTwo
  have hEight : 8 * Λ ^ 3 ≤ (n : ℝ) - 1 := by
    linarith
  have hCube : 0 ≤ Λ ^ 3 := pow_nonneg hΛ 3
  have hNum : 4 * Λ ^ 3 * (n : ℝ) ≤ ((n : ℝ) - 1) ^ 2 := by
    have hprod₁ := mul_nonneg (show 0 ≤ 4 * Λ ^ 3 by positivity)
      (show 0 ≤ 2 * ((n : ℝ) - 1) - (n : ℝ) by linarith)
    have hprod₂ := mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith)
      (show 0 ≤ ((n : ℝ) - 1) - 8 * Λ ^ 3 by linarith)
    nlinarith
  have hden : 0 < ((n : ℝ) - 1) ^ 2 :=
    sq_pos_of_pos (by linarith : (0 : ℝ) < (n : ℝ) - 1)
  refine ⟨hFirst, ?_⟩
  rw [div_le_iff₀ hden]
  nlinarith

end ThLean.W.SA69

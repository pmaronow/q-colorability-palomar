import ThLean.BP.S6.Descent

noncomputable section
open scoped BigOperators

namespace ThLean.W.S641

open ThLean.BP.S6

private theorem shifted_sum_le (M j k : ℕ) (hkj : k ≤ j) (hjM : j ≤ M)
    (b : ℕ → ℕ → ℝ) (hb : ∀ t l, 0 ≤ b t l) :
    (∑ m ∈ Finset.Ico j M, b (m - j + k) k) ≤
      ∑ t ∈ Finset.Ico k M, b t k := by
  let U := M - j + k
  have hku : k ≤ U := by dsimp [U]; omega
  have huM : U ≤ M := by dsimp [U]; omega
  calc
    (∑ m ∈ Finset.Ico j M, b (m - j + k) k) =
        ∑ t ∈ Finset.Ico k U, b t k := by
      apply Finset.sum_bij (fun m _ => m - j + k)
      · intro m hm
        simp only [Finset.mem_Ico] at hm ⊢
        dsimp [U]
        omega
      · intro m₁ hm₁ m₂ hm₂ heq
        simp only [Finset.mem_Ico] at hm₁ hm₂
        omega
      · intro t ht
        simp only [Finset.mem_Ico] at ht
        refine ⟨t + (j - k), ?_, ?_⟩
        · simp only [Finset.mem_Ico]
          omega
        · omega
      · intro m hm
        rfl
    _ ≤ ∑ t ∈ Finset.Ico k M, b t k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico_right huM)
      intro t ht _
      exact hb t k

private theorem geom_shift_bound (h36 : S6_36Statement) (M k : ℕ) :
    (∑ j ∈ Finset.Ico k M, alpha ^ (j - k)) ≤ (4 / 3 : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simpa [alpha] using (h36 0 (M - k)).2.1

theorem S6_38Statement_of_deps (h36 : S6_36Statement) : S6_38Statement := by
  intro M D w b hwd hb
  have hpow : ∀ s : ℕ, 0 ≤ alpha ^ s := (h36 0 0).2.2
  have hterm : ∀ j m k, 0 ≤ alpha ^ (j - k) * b (m - j + k) k := by
    intro j m k
    exact mul_nonneg (hpow _) (hb _ _)
  let J := Finset.Ico (w + 1) M
  let T := fun k => ∑ t ∈ Finset.Ico k M, b t k
  have hJnonneg : ∀ j, 0 ≤
      ∑ m ∈ Finset.Ico j M, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
        alpha ^ (j - k) * b (m - j + k) k := by
    intro j
    apply Finset.sum_nonneg
    intro m hm
    apply Finset.sum_nonneg
    intro k hk
    exact hterm j m k
  have hdrop :
      (∑ j ∈ Finset.Ico (D + 1) M,
        ∑ m ∈ Finset.Ico j M, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
          alpha ^ (j - k) * b (m - j + k) k) ≤
      ∑ j ∈ J,
        ∑ m ∈ Finset.Ico j M, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
          alpha ^ (j - k) * b (m - j + k) k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_left (by omega))
    intro j hj _
    exact hJnonneg j
  have hswap :
      (∑ j ∈ J, ∑ m ∈ Finset.Ico j M,
        ∑ k ∈ Finset.Ico (w + 1) (j + 1),
          alpha ^ (j - k) * b (m - j + k) k) =
      ∑ j ∈ J, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
        ∑ m ∈ Finset.Ico j M,
          alpha ^ (j - k) * b (m - j + k) k := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Finset.sum_comm
  have hfactor :
      (∑ j ∈ J, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
        ∑ m ∈ Finset.Ico j M,
          alpha ^ (j - k) * b (m - j + k) k) =
      ∑ j ∈ J, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
        alpha ^ (j - k) * (∑ m ∈ Finset.Ico j M, b (m - j + k) k) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.mul_sum]
  have hshift :
      (∑ j ∈ J, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
        alpha ^ (j - k) * (∑ m ∈ Finset.Ico j M, b (m - j + k) k)) ≤
      ∑ j ∈ J, ∑ k ∈ Finset.Ico (w + 1) (j + 1), alpha ^ (j - k) * T k := by
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    have hjM : j ≤ M := (Finset.mem_Ico.mp hj).2.le
    have hkj : k ≤ j := by
      have hk' := Finset.mem_Ico.mp hk
      omega
    exact mul_le_mul_of_nonneg_left (shifted_sum_le M j k hkj hjM b hb) (hpow _)
  have htri :
      (∑ j ∈ J, ∑ k ∈ Finset.Ico (w + 1) (j + 1), alpha ^ (j - k) * T k) =
      ∑ k ∈ J, ∑ j ∈ Finset.Ico k M, alpha ^ (j - k) * T k := by
    simpa [J] using
      (Finset.sum_Ico_Ico_comm (w + 1) M (fun k j => alpha ^ (j - k) * T k)).symm
  have hgeom :
      (∑ k ∈ J, ∑ j ∈ Finset.Ico k M, alpha ^ (j - k) * T k) ≤
      (4 / 3 : ℝ) * ∑ k ∈ J, T k := by
    calc
      (∑ k ∈ J, ∑ j ∈ Finset.Ico k M, alpha ^ (j - k) * T k) ≤
          ∑ k ∈ J, (4 / 3 : ℝ) * T k := by
        apply Finset.sum_le_sum
        intro k hk
        have hT : 0 ≤ T k := by
          apply Finset.sum_nonneg
          intro t ht
          exact hb t k
        calc
          (∑ j ∈ Finset.Ico k M, alpha ^ (j - k) * T k) =
              (∑ j ∈ Finset.Ico k M, alpha ^ (j - k)) * T k := by
                rw [← Finset.sum_mul]
          _ ≤ (4 / 3 : ℝ) * T k :=
            mul_le_mul_of_nonneg_right (geom_shift_bound h36 M k) hT
      _ = (4 / 3 : ℝ) * ∑ k ∈ J, T k := by rw [Finset.mul_sum]
  have htotal :
      (∑ j ∈ Finset.Ico (D + 1) M,
        ∑ m ∈ Finset.Ico j M, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
          alpha ^ (j - k) * b (m - j + k) k) ≤
      (4 / 3 : ℝ) * ∑ k ∈ J, T k := by
    calc
      _ ≤ ∑ j ∈ J, ∑ m ∈ Finset.Ico j M,
          ∑ k ∈ Finset.Ico (w + 1) (j + 1),
            alpha ^ (j - k) * b (m - j + k) k := hdrop
      _ = ∑ j ∈ J, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
          ∑ m ∈ Finset.Ico j M,
            alpha ^ (j - k) * b (m - j + k) k := hswap
      _ = ∑ j ∈ J, ∑ k ∈ Finset.Ico (w + 1) (j + 1),
          alpha ^ (j - k) * (∑ m ∈ Finset.Ico j M, b (m - j + k) k) := hfactor
      _ ≤ ∑ j ∈ J, ∑ k ∈ Finset.Ico (w + 1) (j + 1), alpha ^ (j - k) * T k := hshift
      _ = ∑ k ∈ J, ∑ j ∈ Finset.Ico k M, alpha ^ (j - k) * T k := htri
      _ ≤ (4 / 3 : ℝ) * ∑ k ∈ J, T k := hgeom
  change 2 * _ ≤ (8 / 3 : ℝ) * _
  nlinarith [htotal]

end ThLean.W.S641

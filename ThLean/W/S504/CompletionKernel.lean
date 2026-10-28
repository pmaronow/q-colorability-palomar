import ThLean.BP.S5.Completion

noncomputable section
open scoped BigOperators

namespace ThLean.W.S504
open ThresholdFoundations

theorem S5_29AStatement_holds : ThLean.BP.S5.S5_29AStatement := by
  intro A B _ _ _ _ K hK hrow hcol f g hfg
  change (∑ a : A, f a) / (Fintype.card A : ℝ) ≤
    (∑ b : B, g b) / (Fintype.card B : ℝ)

  have hAposNat : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hBposNat : 0 < Fintype.card B :=
    Fintype.card_pos_iff.mpr (inferInstance : Nonempty B)
  have hApos : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hAposNat
  have hBpos : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast hBposNat

  have hcol' (b : B) :
      (∑ a : A, K a b) = (Fintype.card A : ℝ) / (Fintype.card B : ℝ) := by
    have h := hcol b
    change (∑ a : A, K a b) / (Fintype.card A : ℝ) =
      1 / (Fintype.card B : ℝ) at h
    have hAne : (Fintype.card A : ℝ) ≠ 0 := ne_of_gt hApos
    have hBne : (Fintype.card B : ℝ) ≠ 0 := ne_of_gt hBpos
    field_simp [hAne, hBne] at h ⊢
    linarith

  have hleft : (∑ a : A, f a) = ∑ a : A, ∑ b : B, K a b * f a := by
    calc
      (∑ a : A, f a) = ∑ a : A, (∑ b : B, K a b) * f a := by
        apply Finset.sum_congr rfl
        intro a _
        simp [hrow a]
      _ = ∑ a : A, ∑ b : B, K a b * f a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_mul]

  have hterm (a : A) (b : B) : K a b * f a ≤ K a b * g b := by
    by_cases hzero : K a b = 0
    · simp [hzero]
    · have hpos : 0 < K a b := lt_of_le_of_ne (hK a b) (Ne.symm hzero)
      exact mul_le_mul_of_nonneg_left (hfg a b hpos) (hK a b)

  have hweighted :
      (∑ a : A, ∑ b : B, K a b * f a) ≤
        ∑ a : A, ∑ b : B, K a b * g b := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    exact hterm a b

  have hcollapse :
      (∑ a : A, ∑ b : B, K a b * g b) =
        ((Fintype.card A : ℝ) / (Fintype.card B : ℝ)) * (∑ b : B, g b) := by
    calc
      (∑ a : A, ∑ b : B, K a b * g b) =
          ∑ b : B, ∑ a : A, K a b * g b := by
        rw [Finset.sum_comm]
      _ = ∑ b : B, (∑ a : A, K a b) * g b := by
        apply Finset.sum_congr rfl
        intro b _
        rw [← Finset.sum_mul]
      _ = ∑ b : B, ((Fintype.card A : ℝ) / (Fintype.card B : ℝ)) * g b := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hcol' b]
      _ = ((Fintype.card A : ℝ) / (Fintype.card B : ℝ)) * (∑ b : B, g b) := by
        rw [Finset.mul_sum]

  calc
    (∑ a : A, f a) / (Fintype.card A : ℝ) =
        (∑ a : A, ∑ b : B, K a b * f a) / (Fintype.card A : ℝ) := by
      rw [← hleft]
    _ ≤ (∑ a : A, ∑ b : B, K a b * g b) / (Fintype.card A : ℝ) :=
      div_le_div_of_nonneg_right hweighted (le_of_lt hApos)
    _ = (∑ b : B, g b) / (Fintype.card B : ℝ) := by
      rw [hcollapse]
      have hAne : (Fintype.card A : ℝ) ≠ 0 := ne_of_gt hApos
      have hBne : (Fintype.card B : ℝ) ≠ 0 := ne_of_gt hBpos
      field_simp [hAne, hBne]

end ThLean.W.S504

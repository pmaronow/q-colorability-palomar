import ThLean.BP.S6.Descent

noncomputable section
open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S640

private theorem shifted_sum_le_one (M j w : ℕ) (a : ℕ → ℕ → ℝ) (h : ℕ → ℝ)
    (hwj : w < j) (hjM : j ≤ M)
    (hh : ∀ t, 0 ≤ h t) (hab : ∀ t, t < M → a t w ≤ h t)
    (hsum : (∑ t ∈ Finset.range M, h t) ≤ 1) :
    (∑ m ∈ Finset.Ico j M, a (m - j + w) w) ≤ 1 := by
  classical
  let S := Finset.Ico w (M - j + w)
  have hbij :
      (∑ m ∈ Finset.Ico j M, a (m - j + w) w) =
        ∑ t ∈ S, a t w := by
    apply Finset.sum_bij' (fun m _ => m - j + w) (fun t _ => t - w + j)
    · intro m hm
      change m - j + w ∈ Finset.Ico w (M - j + w)
      simp only [Finset.mem_Ico] at hm ⊢
      constructor <;> omega
    · intro t ht
      simp only [S, Finset.mem_Ico] at ht
      simp only [Finset.mem_Ico]
      constructor <;> omega
    · intro m hm
      simp only [Finset.mem_Ico] at hm
      omega
    · intro t ht
      simp only [S, Finset.mem_Ico] at ht
      omega
    · intro m hm
      rfl
  have hsub : S ⊆ Finset.range M := by
    intro t ht
    simp only [S, Finset.mem_Ico, Finset.mem_range] at ht ⊢
    omega
  calc
    (∑ m ∈ Finset.Ico j M, a (m - j + w) w) = ∑ t ∈ S, a t w := hbij
    _ ≤ ∑ t ∈ S, h t := by
      apply Finset.sum_le_sum
      intro t ht
      apply hab
      simp only [S, Finset.mem_Ico] at ht
      omega
    _ ≤ ∑ t ∈ Finset.range M, h t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro t ht htS
        exact hh t)
    _ ≤ 1 := hsum

private theorem shifted_geometric_bound (D M w : ℕ) (hwd : w < D) :
    (∑ j ∈ Finset.Ico (D + 1) M, alpha ^ (j - w)) ≤
      (4 / 3 : ℝ) * alpha ^ (D + 1 - w) := by
  have hα0 : 0 ≤ alpha := by norm_num [alpha]
  have hαlt : alpha < 1 := by norm_num [alpha]
  let r := D + 1 - w
  let L := M - (D + 1)
  have hreindex :
      (∑ j ∈ Finset.Ico (D + 1) M, alpha ^ (j - w)) =
        ∑ s ∈ Finset.range L, alpha ^ (r + s) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro s hs
    congr 1
    simp only [r]
    omega
  have hgeom : (∑ s ∈ Finset.range L, alpha ^ s) ≤ (4 / 3 : ℝ) := by
    calc
      (∑ s ∈ Finset.range L, alpha ^ s) ≤ (1 - alpha)⁻¹ := by
        simpa using
          (geom_sum_Ico_le_of_lt_one (x := alpha) hα0 hαlt (m := 0) (n := L))
      _ = (4 / 3 : ℝ) := by norm_num [alpha]
  have hfactor :
      (∑ s ∈ Finset.range L, alpha ^ (r + s)) =
        alpha ^ r * ∑ s ∈ Finset.range L, alpha ^ s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [pow_add]
  rw [hreindex, hfactor]
  calc
    alpha ^ r * ∑ s ∈ Finset.range L, alpha ^ s ≤
        alpha ^ r * (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hgeom (pow_nonneg hα0 r)
    _ = (4 / 3 : ℝ) * alpha ^ (D + 1 - w) := by
      simp only [r]
      ring

theorem S6_37Statement_holds : ThLean.BP.S6.S6_37Statement := by
  intro M D w a h wD ha hh hab hsum
  have hα0 : 0 ≤ alpha := by norm_num [alpha]
  have hmain :
      (∑ j ∈ Finset.Ico (D + 1) M,
        ∑ m ∈ Finset.Ico j M, alpha ^ (j - w) * a (m - j + w) w) ≤
        ∑ j ∈ Finset.Ico (D + 1) M, alpha ^ (j - w) := by
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_Ico] at hj
    calc
      (∑ m ∈ Finset.Ico j M, alpha ^ (j - w) * a (m - j + w) w) =
          alpha ^ (j - w) * ∑ m ∈ Finset.Ico j M, a (m - j + w) w := by
            rw [Finset.mul_sum]
      _ ≤ alpha ^ (j - w) * 1 :=
        mul_le_mul_of_nonneg_left
          (shifted_sum_le_one M j w a h (by omega) (by omega) hh hab hsum)
          (pow_nonneg hα0 _)
      _ = alpha ^ (j - w) := by ring
  have hgeo := shifted_geometric_bound D M w wD
  calc
    2 * (∑ j ∈ Finset.Ico (D + 1) M,
      ∑ m ∈ Finset.Ico j M, alpha ^ (j - w) * a (m - j + w) w) ≤
        2 * ∑ j ∈ Finset.Ico (D + 1) M, alpha ^ (j - w) :=
      mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ ≤ 2 * ((4 / 3 : ℝ) * alpha ^ (D + 1 - w)) :=
      mul_le_mul_of_nonneg_left hgeo (by norm_num)
    _ = (8 / 3 : ℝ) * alpha ^ (D + 1 - w) := by ring

end ThLean.W.S640

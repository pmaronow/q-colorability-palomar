module

public import ThLean.BP.S3.Adapters

@[expose] public section

noncomputable section

open scoped BigOperators

namespace ThLean.W.S381

open ThresholdFoundations

theorem S3_02bStatement_holds : ThLean.BP.S3.S3_02bStatement := by
  constructor
  · intro A B _ _ _ _ e f
    change (∑ a : A, f (e a)) / (Fintype.card A : ℝ) =
      (∑ b : B, f b) / (Fintype.card B : ℝ)
    rw [Equiv.sum_comp e, Fintype.card_congr e]
  · intro A B _ _ _ _ f
    change (∑ x : A × B, f x) / (Fintype.card (A × B) : ℝ) =
      (∑ a : A, (∑ b : B, f (a, b)) / (Fintype.card B : ℝ)) /
        (Fintype.card A : ℝ)
    have hsum : (∑ x : A × B, f x) = ∑ a : A, ∑ b : B, f (a, b) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [Fintype.card_prod, Nat.cast_mul, hsum]
    simp only [div_eq_mul_inv]
    calc
      (∑ a : A, ∑ b : B, f (a, b)) *
          ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))⁻¹ =
        ((∑ a : A, ∑ b : B, f (a, b)) * (Fintype.card B : ℝ)⁻¹) *
          (Fintype.card A : ℝ)⁻¹ := by rw [mul_inv]; ring
      _ = (∑ a : A, (∑ b : B, f (a, b)) * (Fintype.card B : ℝ)⁻¹) *
          (Fintype.card A : ℝ)⁻¹ := by rw [Finset.sum_mul]
      _ = (∑ a : A, (∑ b : B, f (a, b)) / (Fintype.card B : ℝ)) /
          (Fintype.card A : ℝ) := by simp [div_eq_mul_inv]

example : ThLean.BP.S3.S3_02bStatement := S3_02bStatement_holds

end ThLean.W.S381

import ThLean.BP.S6.Foundation

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S601

theorem S6_01aStatement_holds : ThLean.BP.S6.S6_01aStatement := by
  intro A inst
  constructor
  · intro f hf
    unfold uniformMean
    apply div_nonneg
    · exact Finset.sum_nonneg fun x hx => hf x
    · exact Nat.cast_nonneg _
  · intro f g hfg
    unfold uniformMean
    apply div_le_div_of_nonneg_right
    · exact Finset.sum_le_sum fun x hx => hfg x
    · exact Nat.cast_nonneg _
  · intro f g
    unfold uniformMean
    rw [Finset.sum_add_distrib, add_div]
  · intro c f
    unfold uniformMean
    rw [← Finset.mul_sum, mul_div_assoc]
  · intro hA c
    unfold uniformMean
    have hcard : (0 : ℝ) < (Fintype.card A : ℝ) := Nat.cast_pos.mpr hA
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel_left₀ c (ne_of_gt hcard)
  · intro P
    constructor
    · unfold uniformProb uniformMean
      apply div_nonneg
      · exact Finset.sum_nonneg fun x hx => by
          unfold indicator
          split <;> norm_num
      · exact Nat.cast_nonneg _
    · by_cases hcard0 : Fintype.card A = 0
      · simp [uniformProb, uniformMean, hcard0]
      · have hcard : (0 : ℝ) < (Fintype.card A : ℝ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard0)
        unfold uniformProb uniformMean
        calc
          (∑ a : A, indicator (P a)) / (Fintype.card A : ℝ) ≤
              (∑ _a : A, (1 : ℝ)) / (Fintype.card A : ℝ) := by
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact Finset.sum_le_sum fun a ha => by
              unfold indicator
              split <;> norm_num
          _ = 1 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
            exact div_self (ne_of_gt hcard)

end ThLean.W.S601

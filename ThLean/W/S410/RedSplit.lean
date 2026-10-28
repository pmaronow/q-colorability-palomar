import ThLean.BP.S4.Finite

noncomputable section
open scoped BigOperators
open ThresholdFoundations

namespace ThLean.W.S410

theorem S4_RED_15AStatement_holds : ThLean.BP.S4.S4_RED_15AStatement := by
  classical
  intro A _ _ R P B s ε hR hs hε hB hnotB
  let t : ℝ := s * ε ^ 2
  let c : ℝ := s * ε
  let E₁ : A → Prop := fun x => P x ∧ t < R x ∧ B x
  let E₂ : A → Prop := fun x => P x ∧ t < R x ∧ ¬ B x
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hB' : uniformProb E₁ ≤ ε := by
    simpa [E₁, t] using hB
  have hnotB' : uniformProb E₂ ≤ ε := by
    simpa [E₂, t] using hnotB
  have hpoint : ∀ x,
      (if P x then min c (R x) else 0) ≤
        t + c * indicator (E₁ x) + c * indicator (E₂ x) := by
    intro x
    by_cases hp : P x
    · simp only [if_pos hp]
      by_cases hhigh : t < R x
      · by_cases hb : B x
        · have hm : min c (R x) ≤ c := min_le_left _ _
          have hfinal : min c (R x) ≤ t + c := by nlinarith [hm, ht0]
          simpa [E₁, E₂, indicator, hp, hhigh, hb] using hfinal
        · have hm : min c (R x) ≤ c := min_le_left _ _
          have hfinal : min c (R x) ≤ t + c := by nlinarith [hm, ht0]
          simpa [E₁, E₂, indicator, hp, hhigh, hb] using hfinal
      · have hlo : R x ≤ t := le_of_not_gt hhigh
        have hm : min c (R x) ≤ t := (min_le_right _ _).trans hlo
        simpa [E₁, E₂, indicator, hp, hhigh] using hm
    · simpa [E₁, E₂, indicator, hp] using ht0
  have hmono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) :
      uniformMean f ≤ uniformMean g := by
    unfold uniformMean
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun x _ => h x)) (by positivity)
  have hmean :
      uniformMean (fun x => if P x then min c (R x) else 0) ≤
        uniformMean (fun x => t + c * indicator (E₁ x) + c * indicator (E₂ x)) :=
    hmono hpoint
  have hmean_rhs :
      uniformMean (fun x => t + c * indicator (E₁ x) + c * indicator (E₂ x)) =
        t + c * uniformProb E₁ + c * uniformProb E₂ := by
    simp [uniformMean, uniformProb, t, c, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      add_div, mul_div_assoc]
  rw [hmean_rhs] at hmean
  have hprob : t + c * uniformProb E₁ + c * uniformProb E₂ ≤ 3 * s * ε ^ 2 := by
    have h1 : c * uniformProb E₁ ≤ c * ε := mul_le_mul_of_nonneg_left hB' (le_of_lt hcpos)
    have h2 : c * uniformProb E₂ ≤ c * ε := mul_le_mul_of_nonneg_left hnotB' (le_of_lt hcpos)
    dsimp [t, c]
    nlinarith [h1, h2]
  exact hmean.trans hprob

end ThLean.W.S410

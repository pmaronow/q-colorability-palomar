module

public import ThLean.BP.S4.Finite

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S407

open ThresholdFoundations

/-- The two minimum estimates from P2-ALG-01. -/
theorem S4_ALG_01Statement_holds : ThLean.BP.S4.S4_ALG_01Statement := by
  constructor
  · intro a w y ha haw hy
    by_cases hya : y ≤ a
    · rw [min_eq_right hya, min_eq_right (hya.trans haw)]
      have hratio : 1 ≤ w / a := (one_le_div₀ ha).2 haw
      nlinarith [mul_nonneg (sub_nonneg.mpr hratio) hy]
    · have hay : a ≤ y := le_of_not_ge hya
      rw [min_eq_left hay]
      have hcancel : w / a * a = w := by
        field_simp [ne_of_gt ha]
      rw [hcancel]
      exact min_le_left w y
  · intro a x y ha hx hy
    by_cases hxy : x < y
    · change min a y ≤ x + a * (if x < y then 1 else 0)
      simp only [if_pos hxy, mul_one]
      exact le_trans (min_le_left a y) (by linarith)
    · have hyx : y ≤ x := le_of_not_gt hxy
      change min a y ≤ x + a * (if x < y then 1 else 0)
      simp only [if_neg hxy, mul_zero, add_zero]
      exact (min_le_right a y).trans hyx

example : ThLean.BP.S4.S4_ALG_01Statement := S4_ALG_01Statement_holds

end ThLean.W.S407

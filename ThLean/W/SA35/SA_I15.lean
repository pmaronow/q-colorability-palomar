import ThLean.BP.SA.Interpolation

namespace ThLean.W.SA35

/-- The interpolation square identity and its nonnegativity. -/
theorem SA_I15Statement_holds : ThLean.BP.SA.SA_I15Statement := by
  intro a b r s hr hs
  have hsum : 0 < r + s := add_pos hr hs
  have hden : 0 < r * s * (r + s) := mul_pos (mul_pos hr hs) hsum
  have heq : a ^ 2 / r + b ^ 2 / s - (a + b) ^ 2 / (r + s) =
      (s * a - r * b) ^ 2 / (r * s * (r + s)) := by
    field_simp [ne_of_gt hr, ne_of_gt hs, ne_of_gt hsum]
    ring
  constructor
  · exact heq
  · rw [heq]
    exact div_nonneg (sq_nonneg _) (le_of_lt hden)

end ThLean.W.SA35

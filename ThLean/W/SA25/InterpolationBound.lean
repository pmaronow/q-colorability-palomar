import ThLean.BP.SA.Interpolation

noncomputable section
open scoped BigOperators

namespace ThLean.W.SA25

open ThLean.BP.SA

/-- A bounded insertion increment has expectation at most twice the bound.
This uses the support-law leaf for positivity and normalization of the weights. -/
theorem SA_I12cStatement_of_deps (h : SA_I11cStatement) : SA_I12cStatement := by
  intro D _ _ F rate e B hrate hB hF
  obtain ⟨hweight, htotal, _⟩ := h D rate hrate
  have hincrement (T : Finset D) :
      |F (insert e T) - F T| ≤ 2 * B := by
    calc
      |F (insert e T) - F T| ≤ |F (insert e T)| + |F T| := abs_sub _ _
      _ ≤ B + B := add_le_add (hF _) (hF _)
      _ = 2 * B := by ring
  calc
    |supportMean (fun T => F (insert e T) - F T) rate| =
        |∑ T ∈ Finset.univ.powerset,
          supportWeight rate T * (F (insert e T) - F T)| := rfl
    _ ≤ ∑ T ∈ Finset.univ.powerset,
        |supportWeight rate T * (F (insert e T) - F T)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ Finset.univ.powerset, supportWeight rate T * (2 * B) := by
      apply Finset.sum_le_sum
      intro T hT
      rw [abs_mul, abs_of_nonneg (hweight T)]
      exact mul_le_mul_of_nonneg_left (hincrement T) (hweight T)
    _ = (∑ T ∈ Finset.univ.powerset, supportWeight rate T) * (2 * B) := by
      rw [Finset.sum_mul]
    _ = 2 * B := by rw [htotal]; ring

end ThLean.W.SA25

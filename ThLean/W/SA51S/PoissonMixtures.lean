import ThLean.W.SA51S.Local

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA51S
open ThresholdFoundations ThLean.BP.SA

/-- Both insertion mixtures have the stated graph laws, without additional premises. -/
theorem SA_R70bStatement_holds : ThLean.BP.SA.SA_R70bStatement := by
  intro q n₁ n₂ _hq hn₁ hn₂ c hc
  have h₁ : (0 : ℝ) < n₁ := by exact_mod_cast (show 0 < n₁ by omega)
  have h₂ : (0 : ℝ) < n₂ := by exact_mod_cast (show 0 < n₂ by omega)
  have hz : 0 ≤ c * (n₁+n₂ : ℕ) := by positivity
  refine ⟨fun m => poisson_nonneg hz m, ?_, ?_, global_mixture q n₁ n₂ c,
    local_mixture q n₁ n₂ hn₁ hn₂ c hc⟩
  · apply poisson_summable_bounded hz
    intro m
    have hg : globalStep n₁ n₂ = ⇑(edgeOp (n₁+n₂)) := rfl
    rw [hg, ← edgeOp_iterate]
    exact edge_iterate_bounds q (n₁+n₂) m (by omega) 0
  · simp_rw [local_binomial, Nat.cast_add]
    apply poisson_convolution_summable c (n₁ : ℝ) (n₂ : ℝ) h₁ h₂
      (fun m => (edgeOp n₁ ^ m) (fun G => indicator (Colorable q G)) 0)
      (fun m => (edgeOp n₂ ^ m) (fun G => indicator (Colorable q G)) 0)
    · exact poisson_summable_bounded (mul_nonneg hc h₁.le) _
        (fun m => edge_iterate_bounds q n₁ m hn₁ 0)
    · exact poisson_summable_bounded (mul_nonneg hc h₂.le) _
        (fun m => edge_iterate_bounds q n₂ m hn₂ 0)

example : ThLean.BP.SA.SA_R70bStatement := SA_R70bStatement_holds

end ThLean.W.SA51S

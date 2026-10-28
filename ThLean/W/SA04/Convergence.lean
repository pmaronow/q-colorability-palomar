import ThLean.BP.SA.Convergence

noncomputable section

open Filter
open scoped Topology
open ThresholdFoundations

namespace ThLean.W.SA04

/-- The fixed-level limits agree by the two-level quantile sandwich. -/
theorem SA_C62aStatement_of_deps
    (h01 : ThLean.BP.SA.SA_F01Statement)
    (h03 : ThLean.BP.SA.SA_F03Statement) :
    ThLean.BP.SA.SA_C62aStatement := by
  intro q hq Λ hΛ hlevel
  obtain ⟨_, _, hparam⟩ := h01 q hq
  obtain ⟨_, hηzero, hηsmall, hfrac⟩ := hparam Λ hΛ
  obtain ⟨α₀, hα₀, hlow₀, hupp₀⟩ := hlevel (etaZero Λ) hηzero le_rfl
  refine ⟨α₀, hα₀, ?_⟩
  intro η hη hηle
  obtain ⟨αη, _, hlowη, huppη⟩ := hlevel η hη hηle
  have hhalf : etaZero Λ ≤ (1 / 2 : ℝ) :=
    le_of_lt (lt_trans hηsmall hfrac)
  change Tendsto (fun n : ℕ => (lowerLocation q Λ η n : ℝ) / n)
    atTop (𝓝 αη) at hlowη
  change Tendsto (fun n : ℕ => (lowerLocation q Λ (etaZero Λ) n : ℝ) / n)
    atTop (𝓝 α₀) at hlow₀
  have hlowη' : Tendsto (fun n : ℕ => (lowerLocation q Λ η n : ℝ) / n)
      atTop (𝓝 αη) := hlowη
  have hlow₀' : Tendsto (fun n : ℕ => (lowerLocation q Λ (etaZero Λ) n : ℝ) / n)
      atTop (𝓝 α₀) := hlow₀
  have hle₁ : (fun n : ℕ => (lowerLocation q Λ η n : ℝ) / n) ≤ᶠ[atTop]
      (fun n : ℕ => (lowerLocation q Λ (etaZero Λ) n : ℝ) / n) := by
    filter_upwards [eventually_atTop.2 ⟨2 * q, fun n hn => hn⟩] with n hn
    have hcmp := h03 q hq Λ hΛ n hn η (etaZero Λ) hη hηle hhalf
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcmp.1) (Nat.cast_nonneg n)
  have hle₂ : (fun n : ℕ => (lowerLocation q Λ (etaZero Λ) n : ℝ) / n) ≤ᶠ[atTop]
      (fun n : ℕ => (upperLocation q Λ η n : ℝ) / n) := by
    filter_upwards [eventually_atTop.2 ⟨2 * q, fun n hn => hn⟩] with n hn
    have hcmp := h03 q hq Λ hΛ n hn η (etaZero Λ) hη hηle hhalf
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcmp.2) (Nat.cast_nonneg n)
  have hηle₀ : αη ≤ α₀ := le_of_tendsto_of_tendsto hlowη' hlow₀' hle₁
  have h₀leη : α₀ ≤ αη := le_of_tendsto_of_tendsto hlow₀' huppη hle₂
  have hαeq : αη = α₀ := le_antisymm hηle₀ h₀leη
  exact ⟨by simpa [hαeq] using hlowη, by simpa [hαeq] using huppη⟩

example (h01 : ThLean.BP.SA.SA_F01Statement)
    (h03 : ThLean.BP.SA.SA_F03Statement) :
    ThLean.BP.SA.SA_C62aStatement :=
  SA_C62aStatement_of_deps h01 h03

end ThLean.W.SA04

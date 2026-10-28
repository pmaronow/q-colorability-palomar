import ThLean.BP.SA.Basics
import ThLean.BP.SA.Quantiles

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA47
open ThresholdFoundations ThLean.BP.SA

theorem SA_Q25Statement_of_deps
    (hQ22b : SA_Q22bStatement) (hF01 : SA_F01Statement) :
    SA_Q25Statement := by
  intro q n hq hn Λ η K c δ n₁ hΛ hδ hη hη₀ hw hn₁ hc hcΛ hUcap htail hrho
  rcases hF01 q hq with ⟨_, _, hparams⟩
  rcases hparams Λ hΛ with ⟨_, _, hηsmall, hsmallhalf⟩
  have hηhalf : η ≤ (1 / 2 : ℝ) :=
    le_trans hη₀ (le_of_lt (lt_trans hηsmall hsmallhalf))
  have hfirst :
      c * ((n : ℝ) - 1) < (upperLocation q Λ η n : ℝ) + poissonDeviation n := by
    by_contra hnot
    have hbad :
        (upperLocation q Λ η n : ℝ) + poissonDeviation n ≤ c * ((n : ℝ) - 1) :=
      le_of_not_gt hnot
    have hQ := hQ22b q n hq hn Λ η c hΛ hη hηhalf hc hcΛ hUcap hbad
    have hηtail : η + poissonTailError Λ n ≤ 2 * η := by
      linarith
    have h2η : 2 * η ≤ 2 * etaZero Λ := by
      nlinarith
    have hEtaZero : 2 * etaZero Λ = Real.exp (-2 * Λ) / 4 := by
      simp [etaZero]
      ring
    have hρsmall : rho q n c ≤ Real.exp (-2 * Λ) / 4 := by
      calc
        rho q n c ≤ η + poissonTailError Λ n := hQ
        _ ≤ 2 * η := hηtail
        _ ≤ 2 * etaZero Λ := h2η
        _ = Real.exp (-2 * Λ) / 4 := hEtaZero
    have hexp : 0 < Real.exp (-2 * Λ) := Real.exp_pos _
    linarith
  rcases hw with ⟨_, hwindow⟩
  have hnwindow : max (2 * q) n₁ ≤ n := by omega
  have hwin := hwindow n hnwindow
  have hUwindow :
      (upperLocation q Λ η n : ℝ) ≤
        (lowerLocation q Λ η n : ℝ) + K * (n : ℝ) * δ n := by
    change (upperLocation q Λ η n : ℝ) - (lowerLocation q Λ η n : ℝ) ≤ _ at hwin
    linarith
  have hU :
      c * ((n : ℝ) - 1) <
        (lowerLocation q Λ η n : ℝ) + K * (n : ℝ) * δ n + poissonDeviation n := by
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hdiv :=
    (div_lt_div_iff_of_pos_right hnR).2 hU
  have hleft :
      c * ((n : ℝ) - 1) / (n : ℝ) = c - c / (n : ℝ) := by
    field_simp [ne_of_gt hnR]
  have hright :
      ((lowerLocation q Λ η n : ℝ) + K * (n : ℝ) * δ n + poissonDeviation n) /
          (n : ℝ) =
        (lowerLocation q Λ η n : ℝ) / (n : ℝ) + K * δ n +
          (poissonDeviation n : ℝ) / (n : ℝ) := by
    field_simp [ne_of_gt hnR]
  rw [hleft, hright] at hdiv
  have hratio : c / (n : ℝ) ≤ Λ / (n : ℝ) :=
    div_le_div_of_nonneg_right hcΛ (le_of_lt hnR)
  have hshift : c - Λ / (n : ℝ) ≤ c - c / (n : ℝ) := by
    linarith
  refine ⟨hfirst, ?_⟩
  change c - Λ / (n : ℝ) - K * δ n - (poissonDeviation n : ℝ) / (n : ℝ) <
    (lowerLocation q Λ η n : ℝ) / (n : ℝ)
  linarith

end ThLean.W.SA47

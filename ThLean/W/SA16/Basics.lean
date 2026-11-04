module

public import ThLean.BP.SA.Basics

@[expose] public section

noncomputable section

namespace ThLean.W.SA16

open ThresholdFoundations

/-- The elementary parameter bounds required by the SA blueprint. -/
theorem SA_F01Statement_holds : ThLean.BP.SA.SA_F01Statement := by
  intro q hq
  have hq1 : 1 < q := by omega
  have hq1r : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq2 : 2 ≤ q := by omega
  have hden : 0 < (q : ℝ) - 1 := by linarith
  have hden1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    linarith
  have hratio : 1 < (q : ℝ) / ((q : ℝ) - 1) := by
    rw [lt_div_iff₀ hden]
    linarith
  have hlogden : 0 < Real.log ((q : ℝ) / ((q : ℝ) - 1)) := Real.log_pos hratio
  have hratio_le : (q : ℝ) / ((q : ℝ) - 1) ≤ (q : ℝ) := by
    rw [div_le_iff₀ hden]
    have hprod := mul_le_mul_of_nonneg_left hden1 (show 0 ≤ (q : ℝ) by linarith)
    nlinarith
  have hlogle : Real.log ((q : ℝ) / ((q : ℝ) - 1)) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by positivity) hratio_le
  have hgamma : 1 ≤ gamma q := by
    unfold gamma
    apply (le_div_iff₀ hlogden).2
    nlinarith
  refine ⟨hlogden, hgamma, ?_⟩
  intro Λ hΛ
  have hΛpos : 0 < Λ := by linarith
  refine ⟨hΛpos, ?_, ?_, by norm_num⟩
  · unfold etaZero
    positivity
  · unfold etaZero
    have hexp : Real.exp (-2 * Λ) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith

end ThLean.W.SA16

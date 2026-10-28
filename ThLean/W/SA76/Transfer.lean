import ThLean.BP.SA.Transfer

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThLean.W.SA76

theorem SA_X57Statement_holds : ThLean.BP.SA.SA_X57Statement := by
  intro Ω m P hP X hX hX2 t ht
  have hcheb :
      P {ω | t ≤ |X ω - ∫ ω, X ω ∂P|} ≤
        ENNReal.ofReal (ProbabilityTheory.variance X P / t ^ 2) := by
    exact ProbabilityTheory.meas_ge_le_variance_div_sq hX2 ht
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
  have hvar :
      ProbabilityTheory.variance X P =
        ∫ ω, (X ω - ∫ ω', X ω' ∂P) ^ 2 ∂P := by
    rw [ProbabilityTheory.variance_eq_integral hX.aemeasurable]
  have hnonneg :
      0 ≤ ProbabilityTheory.variance X P / t ^ 2 :=
    div_nonneg (ProbabilityTheory.variance_nonneg X P) (sq_nonneg t)
  have hnonneg' :
      0 ≤ (∫ ω, (X ω - ∫ ω', X ω' ∂P) ^ 2 ∂P) / t ^ 2 := by
    rw [← hvar]
    exact hnonneg
  change (P {ω | t ≤ |X ω - ∫ ω, X ω ∂P|}).toReal ≤ _
  rw [hvar, ENNReal.toReal_ofReal hnonneg'] at hreal
  exact hreal

end ThLean.W.SA76

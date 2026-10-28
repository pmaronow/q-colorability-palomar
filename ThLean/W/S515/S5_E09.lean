import ThLean.BP.S5.Elementary
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace ThLean.W.S515

/-- P3-LOW-E09: logarithmic powers are dominated by every positive power. -/
theorem S5_E09Statement_holds : ThLean.BP.S5.S5_E09Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b ha
    have h := (isLittleO_log_rpow_rpow_atTop b ha).tendsto_div_nhds_zero
    apply (h.comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hlt : ¬ n < 3 := by omega
    simp [hlt]
  · intro a ha
    exact (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  · exact Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

example : ThLean.BP.S5.S5_E09Statement := S5_E09Statement_holds

end ThLean.W.S515

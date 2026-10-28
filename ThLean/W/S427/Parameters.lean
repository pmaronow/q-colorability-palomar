import ThLean.BP.S4.Parameters
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ThLean.W.S427

theorem S4_PAR_02Statement_holds : ThLean.BP.S4.S4_PAR_02Statement := by
  constructor
  · exact Real.exp_one_lt_three
  · exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
      Real.exp_one_lt_three

example : ThLean.BP.S4.S4_PAR_02Statement :=
  S4_PAR_02Statement_holds

end ThLean.W.S427

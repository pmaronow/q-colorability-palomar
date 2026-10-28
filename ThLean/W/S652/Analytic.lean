import ThLean.BP.S6.Analytic

namespace ThLean.W.S652

/-- The numerical exponential estimate used in the high degree parameters. -/
theorem S6_X05Statement_holds : ThLean.BP.S6.S6_X05Statement := by
  constructor
  · exact (Real.one_lt_exp_iff).2 zero_lt_one
  · exact lt_trans Real.exp_one_lt_d9 (by norm_num)

end ThLean.W.S652

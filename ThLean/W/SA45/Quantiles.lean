module

public import ThLean.BP.SA.Quantiles

@[expose] public section

noncomputable section

namespace ThLean.W.SA45

theorem SA_Q23cStatement_holds : ThLean.BP.SA.SA_Q23cStatement := by
  change Summable (fun k : ℕ => (k + 1 : ℝ) * Real.exp (-(k + 1 : ℝ) / 2))
  have hbase : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(1 / 2 : ℝ) * n)) := by
    simpa only [pow_one] using
      (Real.summable_pow_mul_exp_neg_nat_mul 1 (r := 1 / 2) (by norm_num))
  have hshift := (summable_nat_add_iff
    (f := fun n : ℕ => (n : ℝ) * Real.exp (-(1 / 2 : ℝ) * n)) 1).mpr hbase
  refine hshift.congr fun k => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  congr 2
  ring

end ThLean.W.SA45

import ThLean.BP.SA.Tree

noncomputable section

namespace ThLean.W.SA14

theorem SA_E05Statement_holds : ThLean.BP.SA.SA_E05Statement := by
  intro p hp
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) :=
    (Real.summable_nat_rpow_inv).2 hp
  have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ p)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ p)⁻¹) 1).2 hbase
  convert hshift using 1
  ext n
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast]
  exact Real.rpow_neg (by positivity) p

end ThLean.W.SA14

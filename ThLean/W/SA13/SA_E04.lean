import ThLean.BP.SA.Tree

noncomputable section

open Filter
open scoped BigOperators Topology

namespace ThLean.W.SA13

theorem SA_E04Statement_holds : ThLean.BP.SA.SA_E04Statement := by
  intro r hr0 hr1 d
  have hsum : Summable (fun k : ℕ => (k : ℝ) ^ d * r ^ k) := by
    exact summable_pow_mul_geometric_of_norm_lt_one d (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  refine ⟨hsum, ?_⟩
  simpa [Nat.add_comm] using
    (_root_.tendsto_sum_nat_add (f := fun n : ℕ => (n : ℝ) ^ d * r ^ n))

example : ThLean.BP.SA.SA_E04Statement := SA_E04Statement_holds

end ThLean.W.SA13

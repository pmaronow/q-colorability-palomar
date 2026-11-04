module

public import ThLean.BP.SA.Transfer

@[expose] public section

open Filter

namespace ThLean.W.SA80

/-- A fixed nonnegative density is eventually in the binomial graph domain. -/
theorem SA_X59bStatement_holds : ThLean.BP.SA.SA_X59bStatement := by
  intro d hd
  refine Filter.eventually_atTop.2 ⟨Nat.ceil d + 1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hceil : Nat.ceil d ≤ n := by omega
  refine ⟨hnpos, ?_⟩
  exact le_trans (Nat.le_ceil d) (by exact_mod_cast hceil)

end ThLean.W.SA80

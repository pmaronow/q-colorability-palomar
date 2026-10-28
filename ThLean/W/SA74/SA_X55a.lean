import ThLean.BP.SA.Transfer

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA74
open ThresholdFoundations

theorem SA_X55aStatement_holds : ThLean.BP.SA.SA_X55aStatement := by
  intro B m hm p
  constructor
  · change (∑ j ∈ Finset.range (B + 1),
      binomialWeight B p j * indicator (j ≤ m)) = _
    simp only [indicator, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : (Finset.range (B + 1)).filter (fun j : ℕ => j ≤ m) =
        Finset.range (m + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilter]
  · change (∑ j ∈ Finset.range (B + 1),
      binomialWeight B p j * indicator (j < m)) = _
    simp only [indicator, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : (Finset.range (B + 1)).filter (fun j : ℕ => j < m) =
        Finset.range m := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilter]

end ThLean.W.SA74

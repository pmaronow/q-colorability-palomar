module

public import ThLean.W.SA20.Interpolation
public import ThLean.W.SA20S.Histogram

@[expose] public section

noncomputable section

namespace ThLean.W.SA20S

/-- Joint marked-Poisson count factorization, including signed means. -/
theorem SA_I11aStatement_holds : ThLean.BP.SA.SA_I11aStatement := by
  apply ThLean.W.SA20.SA_I11aStatement_of_histogram
  · intro D _ _ ν k z
    exact weighted_histogram ν k z
  · intro D _ _ ν μ z hsum
    exact poisson_product_factor ν μ z hsum

end ThLean.W.SA20S

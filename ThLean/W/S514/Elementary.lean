import ThLean.BP.S5.Elementary

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ThLean.W.S514

theorem S5_E08Statement_holds : ThLean.BP.S5.S5_E08Statement := by
  constructor
  · intro X I _ _ μ f hf
    exact MeasureTheory.lintegral_tsum hf
  · constructor
    · intro X _ μ f hfm hfinite
      have htop : ∀ᵐ x ∂μ, f x < ∞ := MeasureTheory.ae_lt_top' hfm hfinite
      refine ⟨htop.mono (fun x hx => ne_of_lt hx),
        MeasureTheory.integrable_toReal_of_lintegral_ne_top hfm hfinite,
        MeasureTheory.integral_toReal hfm htop⟩
    · intro A I _ _ _ f
      simp only [ThresholdFoundations.uniformMean]
      rw [Finset.sum_comm, Finset.sum_div]

end ThLean.W.S514

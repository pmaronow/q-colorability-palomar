module

public import ThLean.BP.S3.Tails

@[expose] public section

noncomputable section
open MeasureTheory
universe u

namespace ThLean.W.S351

theorem S3_44Statement_holds : ThLean.BP.S3.S3_44Statement := by
  intro Ω _ μ _ X x θ _hX hI
  constructor
  · intro hθ
    let f : Ω → ℝ := fun ω => Real.exp (θ * (X ω - x))
    have hshift (ω : Ω) : f ω = Real.exp (-θ*x) * Real.exp (θ * X ω) := by
      dsimp [f]
      calc
        Real.exp (θ * (X ω - x)) = Real.exp (θ * X ω + -(θ*x)) := by congr 1; ring_nf
        _ = Real.exp (θ * X ω) * Real.exp (-(θ*x)) := Real.exp_add _ _
        _ = Real.exp (-θ*x) * Real.exp (θ * X ω) := by ring_nf
    have hfI : Integrable f μ := by
      convert hI.const_mul (Real.exp (-θ*x)) using 1
      funext ω
      exact hshift ω
    have hpos : ∀ ω, 0 ≤ f ω := fun ω => (Real.exp_pos _).le
    have hm := hfI.measure_le_integral (ae_of_all μ hpos) (s := {ω | x ≤ X ω}) (fun ω hω => by
      change 1 ≤ Real.exp (θ * (X ω - x))
      rw [← Real.exp_zero, Real.exp_le_exp]
      exact mul_nonneg hθ (sub_nonneg.mpr hω))
    have hn : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg_of_ae (ae_of_all μ hpos)
    have hprob : μ.real {ω | x ≤ X ω} ≤ ∫ ω, f ω ∂μ := by
      have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
      simpa [Measure.real, ENNReal.toReal_ofReal hn] using h'
    calc
      μ.real {ω | x ≤ X ω} ≤ ∫ ω, f ω ∂μ := hprob
      _ = ∫ ω, Real.exp (-θ*x) * Real.exp (θ * X ω) ∂μ := by
        congr 1
        funext ω
        exact hshift ω
      _ = Real.exp (-θ*x) * ∫ ω, Real.exp (θ * X ω) ∂μ := integral_const_mul _ _
  · intro hθ
    let f : Ω → ℝ := fun ω => Real.exp (θ * (X ω - x))
    have hshift (ω : Ω) : f ω = Real.exp (-θ*x) * Real.exp (θ * X ω) := by
      dsimp [f]
      calc
        Real.exp (θ * (X ω - x)) = Real.exp (θ * X ω + -(θ*x)) := by congr 1; ring_nf
        _ = Real.exp (θ * X ω) * Real.exp (-(θ*x)) := Real.exp_add _ _
        _ = Real.exp (-θ*x) * Real.exp (θ * X ω) := by ring_nf
    have hfI : Integrable f μ := by
      convert hI.const_mul (Real.exp (-θ*x)) using 1
      funext ω
      exact hshift ω
    have hpos : ∀ ω, 0 ≤ f ω := fun ω => (Real.exp_pos _).le
    have hm := hfI.measure_le_integral (ae_of_all μ hpos) (s := {ω | X ω ≤ x}) (fun ω hω => by
      change 1 ≤ Real.exp (θ * (X ω - x))
      rw [← Real.exp_zero, Real.exp_le_exp]
      exact mul_nonneg_of_nonpos_of_nonpos hθ (sub_nonpos.mpr hω))
    have hn : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg_of_ae (ae_of_all μ hpos)
    have hprob : μ.real {ω | X ω ≤ x} ≤ ∫ ω, f ω ∂μ := by
      have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
      simpa [Measure.real, ENNReal.toReal_ofReal hn] using h'
    calc
      μ.real {ω | X ω ≤ x} ≤ ∫ ω, f ω ∂μ := hprob
      _ = ∫ ω, Real.exp (-θ*x) * Real.exp (θ * X ω) ∂μ := by
        congr 1
        funext ω
        exact hshift ω
      _ = Real.exp (-θ*x) * ∫ ω, Real.exp (θ * X ω) ∂μ := integral_const_mul _ _

example : ThLean.BP.S3.S3_44Statement := S3_44Statement_holds

end ThLean.W.S351

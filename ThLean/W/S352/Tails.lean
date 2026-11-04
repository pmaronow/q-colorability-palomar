module

public import ThLean.BP.S3.Tails

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators Topology

namespace ThLean.W.S352

open ThLean.BP.S3

/-- The exponential moment of the Poisson measure, proved directly from its
atomic integral formula and the exponential series. -/
theorem S3_45Statement_holds : ThLean.BP.S3.S3_45Statement := by
  intro z θ
  constructor
  · rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    have hs : Summable (fun k : ℕ =>
        (Real.exp (-(z : ℝ)) * ((z : ℝ) * Real.exp θ) ^ k) / (k.factorial : ℝ)) := by
      have h := (NormedSpace.expSeries_div_hasSum_exp ((z : ℝ) * Real.exp θ)).summable
      have h' := h.mul_left (Real.exp (-(z : ℝ)))
      simpa [mul_div_assoc] using h'
    apply hs.congr
    intro k
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [show θ * (k : ℝ) = (k : ℝ) * θ by ring, Real.exp_nat_mul, mul_pow]
    ring
  · rw [ProbabilityTheory.integral_poissonMeasure]
    have h := NormedSpace.expSeries_div_hasSum_exp ((z : ℝ) * Real.exp θ)
    have h' := h.mul_left (Real.exp (-(z : ℝ)))
    have hsum : HasSum
        (fun k : ℕ => (Real.exp (-(z : ℝ)) * ((z : ℝ) * Real.exp θ) ^ k) /
          (k.factorial : ℝ))
        (Real.exp (-(z : ℝ)) * Real.exp ((z : ℝ) * Real.exp θ)) := by
      simpa [mul_div_assoc, ← Real.exp_eq_exp_ℝ] using h'
    calc
      ∑' k : ℕ,
          (Real.exp (-(z : ℝ)) * (z : ℝ) ^ k / (k.factorial : ℝ)) *
            Real.exp (θ * (k : ℝ)) =
          ∑' k : ℕ,
            (Real.exp (-(z : ℝ)) * ((z : ℝ) * Real.exp θ) ^ k) /
              (k.factorial : ℝ) := by
        apply tsum_congr
        intro k
        rw [show θ * (k : ℝ) = (k : ℝ) * θ by ring, Real.exp_nat_mul, mul_pow]
        ring
      _ = Real.exp (-(z : ℝ)) * Real.exp ((z : ℝ) * Real.exp θ) := hsum.tsum_eq
      _ = Real.exp ((z : ℝ) * (Real.exp θ - 1)) := by
        rw [← Real.exp_add]
        congr 1
        ring

end ThLean.W.S352

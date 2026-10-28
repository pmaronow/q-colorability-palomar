import ThLean.BP.S3.Poisson

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `lem:pre-tails(a,d)`; blueprint P1-42. -/
def S3_42Statement : Prop :=
  (∀ k : ℕ, 1 ≤ k → ((k : ℝ)/Real.exp 1)^k ≤ (k.factorial : ℝ)) ∧
  (∀ m k : ℕ, 1 ≤ k → (m.choose k : ℝ) ≤ (m : ℝ)^k / k.factorial ∧
    (m : ℝ)^k / k.factorial ≤ (Real.exp 1 * m / k)^k) ∧
  (∀ a b : ℕ, a.factorial * b.factorial ≤ (a+b).factorial)

/-- Paper `lem:pre-tails(a)`; blueprint P1-43. -/
def S3_43Statement : Prop :=
  ∀ (m k : ℕ) (p : ℝ), 1 ≤ k → 0 ≤ p → p ≤ 1 →
    binomialTail m p k ≤ (m.choose k : ℝ) * p^k ∧
    (m.choose k : ℝ) * p^k ≤ (Real.exp 1 * m * p / k)^k

/-- Paper `eq:pre-chernoff`; blueprint P1-44. -/
def S3_44Statement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (x θ : ℝ), Measurable X →
    Integrable (fun ω => Real.exp (θ * X ω)) μ →
    (0 ≤ θ → μ.real {ω | x ≤ X ω} ≤
      Real.exp (-θ*x) * ∫ ω, Real.exp (θ * X ω) ∂μ) ∧
    (θ ≤ 0 → μ.real {ω | X ω ≤ x} ≤
      Real.exp (-θ*x) * ∫ ω, Real.exp (θ * X ω) ∂μ)

/-- Paper `eq:pre-chernoff`; blueprint P1-45. -/
def S3_45Statement : Prop :=
  ∀ (z : NNReal) (θ : ℝ),
    Integrable (fun k : ℕ => Real.exp (θ*k)) (ProbabilityTheory.poissonMeasure z) ∧
    (∫ k : ℕ, Real.exp (θ*k) ∂ProbabilityTheory.poissonMeasure z) =
      Real.exp ((z : ℝ) * (Real.exp θ - 1))

/-- Paper `lem:pre-tails(c)`; blueprint P1-46. -/
def S3_46Statement : Prop :=
  (∀ x : ℝ, 0 ≤ x → x^2/(2*(1+x)) ≤ entropy x) ∧
  (∀ x : ℝ, 0 ≤ x → x < 1 → x^2/2 ≤ entropy (-x))

/-- Paper `lem:pre-tails(b)`; blueprint P1-47. -/
def S3_47Statement : Prop :=
  ∀ z k : ℝ, 0 ≤ z → z < k →
    poissonEvent z (fun n => k ≤ (n : ℝ)) ≤ (Real.exp 1 * z / k) ^ k

/-- Paper `lem:pre-tails(c)`; blueprint P1-48. -/
def S3_48Statement : Prop :=
  ∀ z s : ℝ, 0 < z → 0 < s →
    poissonEvent z (fun n => z+s ≤ (n : ℝ)) ≤ Real.exp (-(s^2)/(2*(z+s)))

/-- Paper `lem:pre-tails(c)`; blueprint P1-49. -/
def S3_49Statement : Prop :=
  ∀ z s : ℝ, 0 < z → 0 < s →
    poissonEvent z (fun n => (n : ℝ) ≤ z-s) ≤ Real.exp (-(s^2)/(2*z))

/-- Paper `lem:pre-tails(d)`; blueprint P1-50. -/
def S3_50Statement : Prop :=
  ∀ (z : ℝ) (i : ℕ), 0 ≤ z → 1 ≤ i →
    poissonTail z i ≤ (Real.exp z - 1) * poissonWeight z (i-1) ∧
    (∀ j : ℕ, 1 ≤ j →
      poissonWeight z (i-1+j) ≤ poissonWeight z (i-1) * z^j / j.factorial) ∧
    Summable (fun j : ℕ => poissonWeight z (i+j)) ∧
    Summable (fun j : ℕ => poissonWeight z (i-1) * z^(j+1) / (j+1).factorial)

/-- Paper `lem:pre-tails`; blueprint P1-51. -/
def S3_51Statement : Prop :=
  S3_43Statement ∧ S3_47Statement ∧ S3_48Statement ∧ S3_49Statement ∧ S3_50Statement
theorem S3_51_assembly (h43 : S3_43Statement) (h47 : S3_47Statement)
    (h48 : S3_48Statement) (h49 : S3_49Statement) (h50 : S3_50Statement) :
    S3_51Statement := ⟨h43,h47,h48,h49,h50⟩

end ThLean.BP.S3

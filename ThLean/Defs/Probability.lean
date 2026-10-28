import Mathlib

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

def indicator (P : Prop) : ℝ := if P then 1 else 0

def uniformMean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card A : ℝ)

def uniformProb {A : Type*} [Fintype A] (P : A → Prop) : ℝ :=
  uniformMean (fun a => indicator (P a))

/-- Nonnegative expectations never collapse a divergent sum to real zero. -/
def uniformMeanENN {A : Type*} [Fintype A] (f : A → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ a, f a) / (Fintype.card A : ℝ≥0∞)

def variance {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  uniformMean (fun a => (f a - uniformMean f) ^ 2)

end ThresholdFoundations

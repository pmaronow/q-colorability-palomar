import ThLean.BP.S5.Poisson

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.S551

open ThresholdFoundations

/-- Remaining countable-series step: independent Poisson counts indexed by the cells
`Fin D × V` have the same bounded expectation as a Poisson number of uniform cell labels.
The three S5 sibling nodes provide the intended tools for proving this statement. -/
def CellPoissonizationStatement : Prop :=
  ThLean.BP.S5.S5_08AStatement →
  ThLean.BP.S5.S5_E06BStatement →
  ThLean.BP.S5.S5_E08Statement →
  ∀ (V : Type) [Fintype V] [Nonempty V] (D : ℕ) (r : ℝ), 0 ≤ r →
    ∀ f : (V → ℕ) → ℝ, (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      (∑' c : (Fin D × V) → ℕ,
        (∏ p, poissonWeight r (c p)) *
          f (fun v => ∑ a : Fin D, c (a, v))) =
      poissonMixture (D * Fintype.card V * r) (fun j =>
        uniformMean (fun x : Fin j → Fin D × V =>
          f (fun v => (Finset.univ.filter (fun i => (x i).2 = v)).card)))


end ThLean.Contrib.S551

module

public import ThLean.BP.S5.Poisson

@[expose] public section

noncomputable section

namespace ThLean.Contrib.S554

open ThresholdFoundations ThLean.BP.S5
open scoped BigOperators

/-- The finite graph identity underlying S5.12: every frozen partner is counted
at its root, while each frozen unordered pair has two endpoints. -/
def PartnerDoubleCountStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 2 ≤ Fintype.card V →
    ∀ G : MGraph V,
      (∑ a : V, (partnerCount q G a : ℝ)) =
        (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) * kappa q G

/-- An invariant graph law gives the same expected number of frozen partners
at every choice of root. This is the relabeling step in S5.12. -/
def InvariantRootMeanStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ) (ν : PMF (MGraph V)), invariantLaw ν →
    ∀ a b : V,
      lawMean ν (fun G => (partnerCount q G a : ℝ)) =
        lawMean ν (fun G => (partnerCount q G b : ℝ))

end ThLean.Contrib.S554

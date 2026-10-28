import ThLean.BP.S6.Descent

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.S635

/-- Remaining first-failure conversion from the ENNReal terminal sum to the
real finite-history mean of the selected frozen-pair hazard. -/
def S6_32aTerminalIdentityStatement : Prop :=
  ∀ (n q M D : ℕ), 3 ≤ n → 3 ≤ q →
    highTerminalProbability (V := Fin n) q M D =
      ∑ m ∈ Finset.range M,
        meanGraph (n := n) m (kappaKind q (fun G e => highEdge G D e))

/-- Remaining finite first-failure partition identifying total hazard with
failure by the supplied history length. -/
def S6_32aHazardEventIdentityStatement : Prop :=
  ∀ (n q M : ℕ), 3 ≤ n → 3 ≤ q →
    (∑ m ∈ Finset.range M, meanGraph (n := n) m (kappa q)) =
      uniformProb (fun x : Hist n M => cappedLast q x < M)

end ThLean.Contrib.S635

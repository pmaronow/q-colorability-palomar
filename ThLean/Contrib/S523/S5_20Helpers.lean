import ThLean.BP.S5.Identification

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.S523
open ThresholdFoundations
open ThLean.BP.S5

/-- Remaining fixed-time split estimate for S5_20.  The unresolved derivation
must split the outside, inside, and crossing edge-count blocks, then identify
the quotient with the outside graph plus the aggregated crossing star. -/
def S5_20SplitBoundStatement : Prop :=
  ∀ q N : ℕ, 3 ≤ q → 3 ≤ N → ∀ Z : Finset (Fin N), Z.Nonempty →
  2 ≤ N - Z.card →
    ∀ s : ℝ, 0 ≤ s →
      poissonGraphMean s (fun G : MGraph (Fin N) =>
        indicator (Colorable q G ∧ ¬ Colorable q (identify G Z))) ≤
      lowEdgeRate N * (Z.card.choose 2 : ℝ) * s +
        addedFailure (V := {v : Fin N // v ∉ Z}) q
          (lowEdgeRate N * s) (Z.card * neighborMean N Z.card s)

/-- Remaining kernel-measurability assembly for S5_20. -/
def S5_20MeasurabilityStatement : Prop :=
  ∀ q N : ℕ, 3 ≤ q → 3 ≤ N → ∀ Z : Finset (Fin N), Z.Nonempty →
  2 ≤ N - Z.card →
    Measurable (fun s : Set.Ici (0 : ℝ) =>
      poissonGraphMean s.val (fun G : MGraph (Fin N) =>
        indicator (Colorable q G ∧ ¬ Colorable q (identify G Z)))) ∧
    Measurable (fun s : Set.Ici (0 : ℝ) =>
      addedFailure (V := {v : Fin N // v ∉ Z}) q
        (lowEdgeRate N * s.val) (Z.card * neighborMean N Z.card s.val))

end ThLean.Contrib.S523

import ThLean.BP.S5.Main

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.S538
open ThresholdFoundations ThLean.BP.S5

/-- The real finite-window mean is the real value of its finite `ENNReal` terminal sum. -/
def S5_42AWindowENNRepresentationStatement : Prop :=
  ∀ q n D : ℕ, 2 * q ≤ n → ∀ y : ℝ, ∀ L U : ℕ,
    windowLow q n D y L U =
      (∑ m ∈ Finset.Ico L U,
        terminalStepENN (V := Fin n) q m
          (fun G e => if lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G then 1 else 0)).toReal

/-- The all-time terminal mass for a low event is finite on the parameter range of the leaf. -/
def S5_42AAllTimeFiniteStatement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 2 * q ≤ n → ∀ y : ℝ,
    terminalMeanENN (V := Fin n) q
      (fun G e => if lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G then 1 else 0) ≠ ∞

end ThLean.Contrib.S538

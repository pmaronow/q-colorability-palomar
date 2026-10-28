import ThLean.BP.S5.Occupation

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.S544
open ThresholdFoundations ThLean.BP.S5

/-- Terminal disintegration and the finite-edge probability-budget bound used
in the `S5_34AStatement` assembly. -/
def S5_34ATerminalDisintegrationStatement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 2 * q + 1 ≤ n → ∀ y : ℝ, 0 < y →
    (∀ m : ℕ, 0 ≤ uniformMean (fun x : EdgeTuple (Fin n) m =>
      lowObservable q D y (tupleGraph x))) ∧
    Summable (fun m => uniformMean (fun x : EdgeTuple (Fin n) m =>
      lowObservable q D y (tupleGraph x))) ∧
    lowTerminalProbability (V := Fin n) q D y =
      ∑' m, uniformMean (fun x : EdgeTuple (Fin n) m =>
        lowObservable q D y (tupleGraph x))

/-- The bridge from the real Poisson occupation contract to the particular
frozen `lowTime` presentation used by the blueprint. -/
def S5_34ALowTimeOccupationStatement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 2 * q + 1 ≤ n → ∀ y : ℝ, 0 < y →
    let a : ℕ → ℝ := fun m => uniformMean (fun x : EdgeTuple (Fin n) m =>
      lowObservable q D y (tupleGraph x))
    (∀ m, 0 ≤ a m) → Summable a →
      IntegrableOn (lowTime q n D y) (Set.Ici 0) ∧
      (∫ t in Set.Ici (0 : ℝ), lowTime q n D y t) = ∑' m, a m

end ThLean.Contrib.S544

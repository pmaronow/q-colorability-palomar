import ThLean.BP.S3.Adapters

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v w

namespace ThLean.Contrib.S390
open ThresholdFoundations ThLean.BP.S3

/-- The ordered-word model and the uniform edge-tuple model give the same
nonnegative expectation. This is the ENNReal form of the word/graph bridge.
-/
def S390GraphListENNStatement : Prop :=
  ∀ (V : Type w) [Fintype V], 2 ≤ Fintype.card V →
  letI : DecidableEq V := Classical.decEq V
  ∀ (t : ℝ) (h : MGraph V → ℝ≥0∞), 0 ≤ t →
    poissonListMeanENN t
      (fun _ : Pair V => 1 / (Fintype.card (Pair V) : ℝ))
      (fun w => h (listGraph w)) = poissonGraphMeanENN t h

/-- The nonnegative ordered-word expectation factors into the two internal
Poisson graph laws and the independent crossing-neighbor list laws.
-/
def S390SplitWordENNStatement : Prop :=
  ∀ (A : Type u) (B : Type v) [Fintype A] [Fintype B],
    3 ≤ Fintype.card (A ⊕ B) → 2 ≤ Fintype.card B →
    letI : DecidableEq (A ⊕ B) := Classical.decEq (A ⊕ B)
    ∀ (t : ℝ) (h : MGraph (A ⊕ B) → ℝ≥0∞), 0 ≤ t →
      poissonListMeanENN t
        (fun _ : Pair (A ⊕ B) => 1 / (Fintype.card (Pair (A ⊕ B)) : ℝ))
        (fun w => h (listGraph w)) =
      poissonGraphMeanENN
        (t * ((Fintype.card A).choose 2 : ℝ) /
          ((Fintype.card (A ⊕ B)).choose 2 : ℝ))
        (fun GA : MGraph A => poissonGraphMeanENN
          (t * ((Fintype.card B).choose 2 : ℝ) /
            ((Fintype.card (A ⊕ B)).choose 2 : ℝ))
          (fun GB : MGraph B => independentPoissonListsMeanENN
            (t * Fintype.card B / ((Fintype.card (A ⊕ B)).choose 2 : ℝ))
            (fun xs : A → List B => h (splitUnionGraph GA GB xs))))

end ThLean.Contrib.S390

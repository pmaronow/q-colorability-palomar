import ThLean.BP.SA.Transfer
import ThLean.BP.SA.Interpolation

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA67
open ThresholdFoundations
open ThLean.BP.SA

private theorem colorable_iff_of_colorings_eq {V : Type*} [Fintype V]
    (q : ℕ) (G G' : MGraph V) (h : colorings q G = colorings q G') :
    Colorable q G ↔ Colorable q G' := by
  constructor
  · rintro ⟨σ, hσ⟩
    have hmem : σ ∈ colorings q G := by
      simp [colorings, hσ]
    have hmem' : σ ∈ colorings q G' := by
      rw [← h]
      exact hmem
    exact ⟨σ, (Finset.mem_filter.mp hmem').2⟩
  · rintro ⟨σ, hσ⟩
    have hmem : σ ∈ colorings q G' := by
      simp [colorings, hσ]
    have hmem' : σ ∈ colorings q G := by
      rw [h]
      exact hmem
    exact ⟨σ, (Finset.mem_filter.mp hmem').2⟩

theorem SA_X50cStatement_of_deps
    (hI : ThLean.BP.SA.SA_I10Statement)
    (hA : ThLean.BP.SA.SA_X50aStatement) :
    ThLean.BP.SA.SA_X50cStatement := by
  intro q n m hq hn hm
  let A : Finset (Sym2 (Fin n)) → Prop := fun E =>
    Colorable q (simpleGraph E)
  have hgeneral := hA n m hn hm A
  have hcolorings := (hI (Fin n) q hq).1
  have hsupp (x : EdgeTuple (Fin n) m) :
      edgeSupport (tupleGraph x) =
        edgeSupport (simpleGraph (edgeSupport (tupleGraph x))) := by
    ext e
    simp only [edgeSupport, simpleGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : 0 < tupleGraph x e <;> simp [h]
  have hevent :
      (fun x : EdgeTuple (Fin n) m =>
        DistinctPrefix x ∧ Colorable q (tupleGraph x)) =
      (fun x => DistinctPrefix x ∧ A (edgeSupport (tupleGraph x))) := by
    funext x
    apply congrArg (fun P : Prop => DistinctPrefix x ∧ P)
    apply propext
    apply colorable_iff_of_colorings_eq
    exact hcolorings (tupleGraph x)
      (simpleGraph (edgeSupport (tupleGraph x))) (hsupp x)
  calc
    uniformProb (fun x : EdgeTuple (Fin n) m =>
        DistinctPrefix x ∧ Colorable q (tupleGraph x)) =
      uniformProb (fun x =>
        DistinctPrefix x ∧ A (edgeSupport (tupleGraph x))) := by
          rw [hevent]
    _ = distinctProbability n m * simpleEvent n m A := hgeneral
    _ = distinctProbability n m * simpleProbability (V := Fin n) q m := by
          rfl

end ThLean.W.SA67

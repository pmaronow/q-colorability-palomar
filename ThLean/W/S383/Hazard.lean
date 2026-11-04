module

public import ThLean.BP.S3.Adapters

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S383

open ThLean.BP.S3 ThresholdFoundations

universe u

private theorem uniformMeanENN_congr' {A : Type*} [Fintype A]
    (f g : A → ℝ≥0∞) (h : ∀ a, f a = g a) :
    uniformMeanENN f = uniformMeanENN g := by
  unfold uniformMeanENN
  apply congrArg (fun s : ℝ≥0∞ => s / (Fintype.card A : ℝ≥0∞))
  exact Finset.sum_congr rfl (fun a _ => h a)

private theorem uniformMeanENN_if_const_mul {A : Type*} [Fintype A]
    (a : ℝ≥0∞) (P : A → Prop) [DecidablePred P] :
    uniformMeanENN (fun x => if P x then a else 0) =
      a * uniformMeanENN (fun x => if P x then 1 else 0) := by
  classical
  have hs : (∑ x ∈ (Finset.univ : Finset A), if P x then a else 0) =
      a * (∑ x ∈ (Finset.univ : Finset A), if P x then 1 else 0) := by
    calc
      (∑ x ∈ (Finset.univ : Finset A), if P x then a else 0) =
          ∑ x ∈ (Finset.univ : Finset A), a * (if P x then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hp : P x <;> simp [hp]
      _ = a * (∑ x ∈ (Finset.univ : Finset A), if P x then 1 else 0) := by
            simpa using (Finset.mul_sum (Finset.univ : Finset A)
              (fun x => if P x then 1 else 0) a).symm
  unfold uniformMeanENN
  change (∑ x ∈ (Finset.univ : Finset A), if P x then a else 0) /
      (Fintype.card A : ℝ≥0∞) =
    a * ((∑ x ∈ (Finset.univ : Finset A), if P x then 1 else 0) /
      (Fintype.card A : ℝ≥0∞))
  rw [hs, mul_div_assoc]

private theorem killing_iff_frozen {V : Type u} [Fintype V] (q : ℕ)
    (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V)
    (h10 : ThLean.BP.S3.S3_10Statement.{u})
    (G : MGraph V) (e : Pair V) :
    (Colorable q G ∧ ¬ Colorable q (addPair G e)) ↔ FrozenPair q G e := by
  have hadd := (h10 V q hq hV).1 G e
  constructor
  · rintro ⟨hG, hfail⟩
    by_contra hnot
    exact hfail (hadd.mpr ⟨hG, hnot⟩)
  · intro hfr
    rcases hfr with ⟨u, v, he, hfreeze⟩
    refine ⟨hfreeze.1, ?_⟩
    intro haddable
    exact (hadd.mp haddable).2 ⟨u, v, he, hfreeze⟩

private theorem killingMeanENN_eq_kappa {V : Type u} [Fintype V] (q : ℕ)
    (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V)
    (h10 : ThLean.BP.S3.S3_10Statement.{u})
    (h02c : ThLean.BP.S3.S3_02cStatement.{u})
    (G : MGraph V) :
    uniformMeanENN (fun e : Pair V =>
      if Colorable q G ∧ ¬ Colorable q (addPair G e) then 1 else 0) =
        ENNReal.ofReal (kappa q G) := by
  have hkind := h02c V hV q (fun _ _ => True) G
  have hkp : uniformMeanENN (fun e : Pair V =>
      if FrozenPair q G e then 1 else 0) = ENNReal.ofReal (kappa q G) := by
    simpa [kappaKindENN, kappaKind, kappa] using hkind
  calc
    uniformMeanENN (fun e : Pair V =>
      if Colorable q G ∧ ¬ Colorable q (addPair G e) then 1 else 0) =
        uniformMeanENN (fun e : Pair V => if FrozenPair q G e then 1 else 0) := by
          apply uniformMeanENN_congr'
          intro e
          simp only [killing_iff_frozen q hq hV h10 G e]
    _ = ENNReal.ofReal (kappa q G) := hkp

/-- The ENNReal hazard identity, derived from the frozen-pair and
`kappaKindENN` adapter leaves. -/
theorem S3_15bStatement_of_deps
    (h10 : ThLean.BP.S3.S3_10Statement.{u})
    (h02c : ThLean.BP.S3.S3_02cStatement.{u}) :
    ThLean.BP.S3.S3_15bStatement.{u} := by
  intro V _ q hq hV m h
  unfold terminalStepENN graphMeanENN
  apply uniformMeanENN_congr'
    (fun x : EdgeTuple V m => uniformMeanENN (fun e : Pair V =>
      if Colorable q (tupleGraph x) ∧
          ¬ Colorable q (addPair (tupleGraph x) e) then h (tupleGraph x) else 0))
    (fun x : EdgeTuple V m => h (tupleGraph x) *
      ENNReal.ofReal (kappa q (tupleGraph x)))
  intro x
  calc
    uniformMeanENN (fun e : Pair V =>
        if Colorable q (tupleGraph x) ∧
            ¬ Colorable q (addPair (tupleGraph x) e) then h (tupleGraph x) else 0) =
      h (tupleGraph x) * uniformMeanENN (fun e : Pair V =>
        if Colorable q (tupleGraph x) ∧
            ¬ Colorable q (addPair (tupleGraph x) e) then 1 else 0) := by
          exact uniformMeanENN_if_const_mul (h (tupleGraph x))
            (fun e => Colorable q (tupleGraph x) ∧
              ¬ Colorable q (addPair (tupleGraph x) e))
    _ = h (tupleGraph x) * ENNReal.ofReal (kappa q (tupleGraph x)) := by
          rw [killingMeanENN_eq_kappa q hq hV h10 h02c (tupleGraph x)]

end ThLean.W.S383

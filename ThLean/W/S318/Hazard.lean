module

public import ThLean.BP.S3.Terminal

@[expose] public section

/-!
The finite-average helpers `uniformMeanENN_congr`
match implementation patterns in OpenAI's math library (Apache-2.0).
Local versions use project-specific averaging definitions and namespaces.
Their source credits and licence scope are listed in NOTICE; the licence
text is in LICENSES/Apache-2.0.txt.
-/

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S318
open ThresholdFoundations ThLean.BP.S3
universe u

private theorem uniformMeanENN_indicator {A : Type*} [Fintype A]
    (hcard : 0 < Fintype.card A) (P : A → Prop) :
    uniformMeanENN (fun a => if P a then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (uniformProb P) := by
  classical
  simp [uniformMeanENN, uniformProb, uniformMean, indicator]
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hcard)]
  simp

private theorem finFilterCard {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ∑ i : Fin n, if P i then 1 else 0 := by
  classical
  calc
    (Finset.univ.filter P).card =
        ∑ i ∈ Finset.univ, if P i then 1 else 0 := by
          simp
    _ = ∑ i : Fin n, if P i then 1 else 0 := by simp

private theorem uniformMeanENN_congr {A : Type*} [Fintype A]
    {f g : A → ℝ≥0∞} (h : ∀ a, f a = g a) :
    uniformMeanENN f = uniformMeanENN g := by
  unfold uniformMeanENN
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

private theorem tupleGraph_snoc {V : Type*} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (e : Pair V) :
    tupleGraph (Fin.snoc (α := fun _ : Fin (m+1) => Pair V) x e) =
      addPair (tupleGraph x) e := by
  classical
  ext f
  change (Finset.univ.filter (fun i : Fin (m+1) =>
      ((Fin.snoc (α := fun _ : Fin (m+1) => Pair V) x e) i).val = f)).card =
    Function.update (tupleGraph x) e.val ((tupleGraph x) e.val + 1) f
  rw [finFilterCard, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  by_cases h : f = e.val
  · subst f
    simp [Function.update]
    rfl
  · have hne : e.val ≠ f := fun hh => h hh.symm
    simp [Function.update, h, hne]
    rfl

theorem S3_15Statement_of_deps
    (h10 : S3_10Statement.{u}) (h14 : S3_14Statement.{u}) :
    S3_15Statement.{u} := by
  intro V instV q hq hV m z
  have hpair : 0 < Fintype.card (Pair V) := by
    have hVpos : 0 < Fintype.card V := by omega
    let a : V := Classical.choice (Fintype.card_pos_iff.mp hVpos)
    obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a
    have hab : a ≠ b := hba.symm
    apply Fintype.card_pos_iff.mpr
    refine ⟨⟨s(a, b), ?_⟩⟩
    intro v hv
    rw [Sym2.eq_iff] at hv
    rcases hv with ⟨hav, hbv⟩ | ⟨hav, hbv⟩
    · exact hab (hav.trans hbv.symm)
    · exact hab (hav.trans hbv.symm)
  let F : EdgeTuple V m → Pair V → ℝ≥0∞ := fun x e =>
    if Colorable q (tupleGraph x) ∧
      ¬ Colorable q (addPair (tupleGraph x) e) then 1 else 0
  have hsnoc (x : EdgeTuple V (m+1)) :
      tupleGraph x = addPair (tupleGraph (initTuple x)) (lastPair x) := by
    have hx : Fin.snoc (α := fun _ : Fin (m+1) => Pair V)
        (initTuple x) (lastPair x) = x := by
      funext i
      exact Fin.lastCases (by simp [lastPair])
        (fun j => by simp [initTuple]) i
    calc
      tupleGraph x = tupleGraph (Fin.snoc (α := fun _ : Fin (m+1) => Pair V)
          (initTuple x) (lastPair x)) := congrArg tupleGraph hx.symm
      _ = addPair (tupleGraph (initTuple x)) (lastPair x) :=
        tupleGraph_snoc (initTuple x) (lastPair x)
  have hfactor := (h14 V hV m).1 z F
  calc
    uniformMeanENN (fun x : EdgeTuple V (m+1) =>
        z (initTuple x) *
          if Colorable q (tupleGraph (initTuple x)) ∧
            ¬ Colorable q (tupleGraph x) then 1 else 0) =
      uniformMeanENN (fun x : EdgeTuple V (m+1) =>
        z (initTuple x) * F (initTuple x) (lastPair x)) := by
          apply uniformMeanENN_congr (A := EdgeTuple V (m+1))
          intro x
          simp [F, hsnoc]
    _ = uniformMeanENN (fun x : EdgeTuple V m =>
        z x * uniformMeanENN (F x)) := hfactor
    _ = uniformMeanENN (fun x : EdgeTuple V m =>
        z x * ENNReal.ofReal (kappa q (tupleGraph x))) := by
          apply uniformMeanENN_congr (A := EdgeTuple V m)
          intro x
          have hprob := ((h10 V q hq hV).2.1 (tupleGraph x))
          have hinner : uniformMeanENN (F x) =
              ENNReal.ofReal (kappa q (tupleGraph x)) := by
            let P : Pair V → Prop := fun e =>
              Colorable q (tupleGraph x) ∧
                ¬ Colorable q (addPair (tupleGraph x) e)
            calc
              uniformMeanENN (F x) = uniformMeanENN (fun e : Pair V =>
                  @ite ℝ≥0∞ (P e) (Classical.propDecidable (P e)) 1 0) := by
                    apply uniformMeanENN_congr (A := Pair V)
                    intro e
                    by_cases he : P e <;> simp [F, P, he]
              _ = ENNReal.ofReal (uniformProb P) := uniformMeanENN_indicator hpair P
              _ = ENNReal.ofReal (kappa q (tupleGraph x)) := by
                    rw [show uniformProb P = kappa q (tupleGraph x) by
                      simpa [P] using hprob]
          exact congrArg (fun a : ℝ≥0∞ => z x * a) hinner

end ThLean.W.S318

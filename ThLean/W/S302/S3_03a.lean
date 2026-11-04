module

public import ThLean.BP.S3.Graph

@[expose] public section

noncomputable section

open scoped BigOperators

namespace ThLean.W.S302
open ThresholdFoundations

private theorem pair_noLoop_iff_not_isDiag {V : Type*} (z : Sym2 V) :
    (∀ v : V, z ≠ s(v, v)) ↔ ¬ z.IsDiag := by
  induction z using Sym2.ind with
  | h a b => simp [eq_comm]

private def pairNoDiagEquiv (V : Type*) :
    Pair V ≃ {z : Sym2 V // ¬ z.IsDiag} where
  toFun e := ⟨e.val, (pair_noLoop_iff_not_isDiag e.val).mp e.property⟩
  invFun e := ⟨e.val, (pair_noLoop_iff_not_isDiag e.val).mpr e.property⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

private def incidentPairEquiv {V : Type*} [DecidableEq V] (u : V) :
    {e : Pair V // Touches u e.val} ≃ {v : V // v ≠ u} where
  toFun e := by
    let v := Classical.choose e.property
    have hv : e.val.val = s(u, v) := Classical.choose_spec e.property
    have hne : v ≠ u := by
      intro h
      apply e.val.property u
      simpa [h] using hv
    exact ⟨v, hne⟩
  invFun v := by
    refine ⟨⟨s(u, v.val), ?_⟩, ?_⟩
    · intro x hx
      have hd : (s(u, v.val)).IsDiag := by
        rw [hx]
        exact Sym2.diag_isDiag x
      exact v.property (Sym2.mk_isDiag_iff.mp hd).symm
    · exact ⟨v.val, rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec e.property).symm
  right_inv v := by
    apply Subtype.ext
    change Classical.choose (show ∃ w : V, s(u, v.val) = s(u, w) from ⟨v.val, rfl⟩) = v.val
    exact (Sym2.congr_right.mp (Classical.choose_spec
      (show ∃ w : V, s(u, v.val) = s(u, w) from ⟨v.val, rfl⟩))).symm

theorem S3_03aStatement_holds : ThLean.BP.S3.S3_03aStatement := by
  classical
  intro V _ hV
  have hcard : Fintype.card (Pair V) = (Fintype.card V).choose 2 := by
    calc
      Fintype.card (Pair V) =
          Fintype.card {z : Sym2 V // ¬ z.IsDiag} :=
        Fintype.card_congr (pairNoDiagEquiv V)
      _ = (Fintype.card V).choose 2 := Sym2.card_subtype_not_diag
  refine ⟨hcard, ?_, ?_⟩
  · rw [hcard]
    exact Nat.choose_pos (by omega)
  · intro u
    have hincident :
        Fintype.card {e : Pair V // Touches u e.val} = Fintype.card V - 1 := by
      calc
        Fintype.card {e : Pair V // Touches u e.val} =
            Fintype.card {v : V // v ≠ u} :=
          Fintype.card_congr (incidentPairEquiv u)
        _ = Fintype.card V - Fintype.card {v : V // v = u} :=
          Fintype.card_subtype_compl (fun v : V => v = u)
        _ = Fintype.card V - 1 := by rw [Fintype.card_subtype_eq u]
    calc
      (Finset.univ.filter (fun e : Pair V => Touches u e.val)).card =
          Fintype.card {e : Pair V // Touches u e.val} := by
        symm
        exact Fintype.card_of_subtype
          (Finset.univ.filter (fun e : Pair V => Touches u e.val)) (by simp)
      _ = Fintype.card V - 1 := hincident

example : ThLean.BP.S3.S3_03aStatement := S3_03aStatement_holds

end ThLean.W.S302

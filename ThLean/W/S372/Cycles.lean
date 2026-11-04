module

public import ThLean.BP.S3.Cycles
public import Mathlib.Data.List.Perm.Subperm

@[expose] public section

noncomputable section

open ThLean.BP.S3
open scoped List

namespace ThLean.W.S372

universe u

private theorem card_positions_eq_count {E : Type u} [Fintype E] [DecidableEq E]
    (l : List E) (e : E) :
    Fintype.card {i : Fin l.length // l.get i = e} = l.count e := by
  classical
  have hc : Fintype.card {i : Fin l.length // l.get i = e} =
      ((List.finRange l.length).toFinset.filter (fun i => l.get i = e)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext i
    simp
  rw [hc]
  rw [List.Nodup.card_eq_countP (List.nodup_finRange _)]
  have hcnt : List.countP (fun i : Fin l.length => decide (l.get i = e))
      (List.finRange l.length) = l.count e := by
    calc
      List.countP (fun i : Fin l.length => decide (l.get i = e))
          (List.finRange l.length) =
          List.countP (fun i : E => decide (i = e))
            (List.map l.get (List.finRange l.length)) := by
              rw [List.countP_map]
              rfl
      _ = l.count e := by
        rw [← List.ofFn_eq_map (f := l.get), List.ofFn_get]
        change List.countP (fun x : E => decide (x = e)) l =
          List.countP (fun x => x == e) l
        congr 1
  exact hcnt

theorem S3_69Statement_holds : ThLean.BP.S3.S3_69Statement := by
  classical
  intro E _ p x
  constructor
  · constructor
    · intro h
      have hs : p <+~ x := (List.subperm_iff_count).2 h
      refine ⟨⟨hs.idxInj, hs.idxInj_injective⟩, ?_⟩
      intro j
      exact (hs.getElem_idxInj_eq_getElem (i := j)).symm
    · rintro ⟨ι, hι⟩ e
      have hinj : Function.Injective (fun i : {j : Fin p.length // p.get j = e} =>
          (⟨ι i.1, by rw [← hι i.1]; exact i.2⟩ : {j : Fin x.length // x.get j = e})) := by
        intro i j hij
        apply Subtype.ext
        exact ι.injective (congrArg Subtype.val hij)
      calc
        p.count e = Fintype.card {j : Fin p.length // p.get j = e} :=
          (card_positions_eq_count p e).symm
        _ ≤ Fintype.card {j : Fin x.length // x.get j = e} :=
          Fintype.card_le_of_injective _ hinj
        _ = x.count e := card_positions_eq_count x e
  · calc
      Fintype.card {ι : Fin p.length ↪ Fin x.length //
          ∀ j, p.get j = x.get (ι j)} ≤
          Fintype.card (Fin p.length → Fin x.length) :=
        Fintype.card_le_of_injective (fun z => (z.1 : Fin p.length → Fin x.length)) (by
          intro a b h
          apply Subtype.ext
          apply Function.Embedding.ext
          intro j
          exact congrFun h j)
      _ = x.length ^ p.length := by simp

end ThLean.W.S372

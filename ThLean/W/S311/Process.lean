module

public import ThLean.BP.S3.Graph
public import ThLean.BP.S3.Process

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S311

open ThresholdFoundations
universe u

private lemma tupleGraph_card_succ {V : Type u} [Fintype V]
    (ω : EdgeStream V) (m : ℕ) (e : Sym2 V) :
    (Finset.univ.filter (fun i : Fin (m + 1) => (ω i).val = e)).card =
      (Finset.univ.filter (fun i : Fin m => (ω i).val = e)).card +
        if (ω m).val = e then 1 else 0 := by
  classical
  simp only [Finset.card_filter, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

private lemma processGraph_succ {V : Type u} [Fintype V]
    (ω : EdgeStream V) (m : ℕ) :
    processGraph ω (m + 1) = addPair (processGraph ω m) (ω m) := by
  classical
  ext e
  change (Finset.univ.filter (fun i : Fin (m + 1) => (ω i).val = e)).card =
    Function.update (tupleGraph (fun i : Fin m => ω i.val)) (ω m).val
      ((tupleGraph (fun i : Fin m => ω i.val)) (ω m).val + 1) e
  rw [tupleGraph_card_succ]
  by_cases he : e = (ω m).val
  · subst e
    simp [tupleGraph, Function.update]
  · have he' : (ω m).val ≠ e := Ne.symm he
    simp [tupleGraph, Function.update, he, he']

private lemma pair_card_ge_two {V : Type u} [Fintype V] (e : Pair V) :
    2 ≤ Fintype.card V := by
  classical
  have hex : ∃ u v : V, e.val = s(u, v) := by
    exact (Sym2.exists (f := fun z : Sym2 V => e.val = z)).mp ⟨e.val, rfl⟩
  rcases hex with ⟨u, v, hpair⟩
  have huv : u ≠ v := by
    intro h
    apply e.property u
    simpa [h] using hpair
  let f : Fin 2 → V := ![u, v]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  exact Fintype.card_le_of_injective f hf

theorem S3_04bStatement_of_deps
    (ha : ThLean.BP.S3.S3_04aStatement.{u})
    (h10 : ThLean.BP.S3.S3_10Statement.{u}) :
    ThLean.BP.S3.S3_04bStatement.{u} := by
  classical
  intro V inst q hq ω h hh
  let haV := ha V q hq
  have hposTop : (1 : WithTop ℕ) ≤ (h : WithTop ℕ) := by
    rw [← hh]
    exact haV.1 ω
  have hpos : 1 ≤ h := by
    exact_mod_cast hposTop
  have hstep : (h - 1) + 1 = h := Nat.sub_add_cancel hpos
  have htime : hittingTime q ω = (((h - 1) + 1 : ℕ) : WithTop ℕ) := by
    rw [hstep]
    exact hh
  rcases (haV.2.1 ω (h - 1)).2.mp htime with ⟨hcolor, hfail⟩
  have hfailCurrent : ¬ Colorable q (processGraph ω h) := by
    simpa [hstep] using hfail
  have hsucc : processGraph ω h =
      addPair (processGraph ω (h - 1)) (ω (h - 1)) := by
    simpa [hstep] using processGraph_succ ω (h - 1)
  have hfailAdd : ¬ Colorable q
      (addPair (processGraph ω (h - 1)) (ω (h - 1))) := by
    rw [← hsucc]
    exact hfailCurrent
  have hcard : 2 ≤ Fintype.card V := pair_card_ge_two (ω (h - 1))
  have hFrozen : FrozenPair q (processGraph ω (h - 1)) (ω (h - 1)) := by
    by_contra hnot
    apply hfailAdd
    exact ((h10 V q hq hcard).1
      (processGraph ω (h - 1)) (ω (h - 1))).mpr ⟨hcolor, hnot⟩
  have hFirst : ∃ m, ¬ Colorable q (processGraph ω m) :=
    ⟨h, hfailCurrent⟩
  have hfind : Nat.find hFirst = h := by
    apply Nat.le_antisymm
    · exact Nat.find_min' hFirst hfailCurrent
    · by_contra hn
      have hlt : Nat.find hFirst < h := by omega
      have hltTop : ((Nat.find hFirst : ℕ) : WithTop ℕ) < hittingTime q ω := by
        rw [hh]
        exact_mod_cast hlt
      have hbefore := (haV.2.1 ω (Nat.find hFirst)).1.mp hltTop
      exact (Nat.find_spec hFirst) hbefore
  have hlast : lastGraph q ω = some (processGraph ω (h - 1)) := by
    unfold lastGraph
    rw [dif_pos hFirst, hfind]
  have hedge : finalEdge q ω = some (ω (h - 1)) := by
    unfold finalEdge
    rw [dif_pos hFirst, hfind]
  exact ⟨hpos, hlast, hedge, hcolor, hFrozen⟩

end ThLean.W.S311

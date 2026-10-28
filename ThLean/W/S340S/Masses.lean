import ThLean.W.S340S.Partition
import ThLean.W.S302.S3_03a
import ThLean.W.S332.PoissonMass
import ThLean.W.S341.PoissonZero

noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S3
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S340S
universe u
set_option maxHeartbeats 800000

theorem finite_splitting (h35 : S3_35aStatement.{u})
    {E I : Type u} [Fintype E] [Nonempty E] [Fintype I] [DecidableEq I]
    (ν : E → ℝ) (label : E → I) (z : ℝ)
    (hν : IsProbabilityVector ν) (hz : 0 ≤ z)
    (hpos : ∀ j, 0 < ∑ e : E, if label e = j then ν e else 0)
    (words : I → List E) (hw : ∀ j e, e ∈ words j → label e = j) :
    weightedListMean z ν
      (fun w => indicator (∀ j, w.filter (fun e => label e = j) = words j)) =
      ∏ j, poissonListMass (z * ∑ e : E, if label e = j then ν e else 0)
        (fun e => ν e / (∑ e : E, if label e = j then ν e else 0)) (words j) := by
  classical
  let r := Fintype.equivFin I
  have hc (j : Fin (Fintype.card I)) :
      cellMass ν (r ∘ label) j = ∑ e : E, if label e = r.symm j then ν e else 0 := by
    simp [cellMass, Function.comp_def, Equiv.apply_eq_iff_eq_symm_apply]
  have hevent (w : List E) :
      (∀ j, splitSublist (r ∘ label) j w = words (r.symm j)) ↔
        ∀ j, w.filter (fun e => label e = j) = words j := by
    simp only [splitSublist,Function.comp_def,Equiv.apply_eq_iff_eq_symm_apply]
    constructor
    · intro h j
      simpa using h (r j)
    · intro h j
      exact h (r.symm j)
  have hs := h35 E ν (Fintype.card I) (r ∘ label) z hν hz
    (fun j => by rw [hc]; exact hpos _) (words ∘ r.symm)
    (fun j e he => by simp [Function.comp_def, hw (r.symm j) e he])
  calc
    _ = weightedListMean z ν (fun w => indicator
        (∀ j, splitSublist (r ∘ label) j w = words (r.symm j))) := by
      congr 1
      funext w
      exact congrArg indicator (propext (hevent w).symm)
    _ = _ := hs
    _ = ∏ j : Fin (Fintype.card I),
        poissonListMass (z * ∑ e : E, if label e = r.symm j then ν e else 0)
          (fun e => ν e / (∑ e : E, if label e = r.symm j then ν e else 0))
          (words (r.symm j)) := by simp_rw [hc]; rfl
    _ = _ := r.symm.prod_comp (fun j : I =>
      poissonListMass (z * ∑ e : E, if label e = j then ν e else 0)
        (fun e => ν e / (∑ e : E, if label e = j then ν e else 0)) (words j))

def blockMass {V : Type u} [Fintype V] (S : Finset V) (j : SplitIndex S) : ℝ :=
  ∑ e : Pair V, if blockLabel S e = j then 1 / (Fintype.card (Pair V) : ℝ) else 0

@[simp] theorem blockMass_out {V : Type u} [Fintype V] (S : Finset V)
    (p : Pair (Outside S)) :
    blockMass S (.inl p) = 1 / (Fintype.card (Pair V) : ℝ) := by
  simp [blockMass,blockLabel_out_iff]

@[simp] theorem blockMass_in {V : Type u} [Fintype V] (S : Finset V)
    (p : Pair (Inside S)) :
    blockMass S (.inr (.inl p)) = 1 / (Fintype.card (Pair V) : ℝ) := by
  simp [blockMass,blockLabel_in_iff]

@[simp] theorem blockMass_cross {V : Type u} [Fintype V] (S : Finset V)
    (a : Inside S) : blockMass S (.inr (.inr a)) =
      ((Finset.univ \ S).card : ℝ) / Fintype.card (Pair V) := by
  unfold blockMass
  rw [← (splitEquiv S).sum_comp]
  change (∑ x : SplitAlphabet S, if blockLabel S (embedSplit S x) = .inr (.inr a)
    then 1 / (Fintype.card (Pair V) : ℝ) else 0) = _
  simp [blockLabel_embed, collapseSplit, Fintype.sum_sum_type,
    Fintype.sum_prod_type, div_eq_mul_inv]

theorem blockMass_pos {V : Type u} [Fintype V] (S : Finset V)
    (hV : 2 ≤ Fintype.card V) (hS : 0 < (Finset.univ \ S).card) :
    ∀ j, 0 < blockMass S j := by
  have hN : 0 < Fintype.card (Pair V) :=
    (ThLean.W.S302.S3_03aStatement_holds V hV).2.1
  rintro (p | p | a) <;> simp only [blockMass_out,blockMass_in,blockMass_cross] <;>
    positivity

theorem uniformPair_probability {V : Type u} [Fintype V]
    (hV : 2 ≤ Fintype.card V) :
    IsProbabilityVector (fun _ : Pair V => 1 / (Fintype.card (Pair V) : ℝ)) := by
  have hN : (Fintype.card (Pair V) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (ThLean.W.S302.S3_03aStatement_holds V hV).2.1
  constructor
  · intro e; positivity
  · simp [hN]

theorem poissonGraph_scaled {V : Type u} [Fintype V]
    (h35 : S3_35aStatement.{u}) (T : Finset V) (G : MGraph (Inside T))
    (hG : Loopless G) (t d : ℝ) (ht : 0 ≤ t) (hd : 0 < d) :
    poissonGraphMean (t * (T.card.choose 2 : ℝ) / d) (fun H => indicator (H = G)) =
      ∏ p : Pair (Inside T), poissonWeight (t / d) (G p.val) := by
  classical
  by_cases hT : 2 ≤ T.card
  · have hcard : Fintype.card (Inside T) = T.card := Fintype.card_coe T
    have hp := ThLean.W.S302.S3_03aStatement_holds (Inside T) (by omega)
    have hpc : Nat.card (Pair (Inside T)) = T.card.choose 2 := by
      simpa only [Fintype.card_eq_nat_card] using
        hp.1.trans (congrArg (fun n : ℕ => n.choose 2) hcard)
    have hpcpos : (Nat.card (Pair (Inside T)) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (show 0 < Nat.card (Pair (Inside T)) by
        rw [hpc]; exact Nat.choose_pos hT)
    have hr : (t * (T.card.choose 2 : ℝ) / d) /
        Nat.card (Pair (Inside T)) = t / d := by
      rw [← hpc]
      field_simp
    rw [ThLean.W.S339.poissonGraph_pointMass_loopless_of_s35a
      ThLean.W.S332.S3_31Statement_holds h35 (by omega) _ (by positivity) G hG]
    rw [ThLean.W.S339.independentMass_eq_pairProduct
      ThLean.W.S332.S3_31Statement_holds _ (by positivity) G hG]
    simp only [Fintype.card_eq_nat_card,hr]
    congr!
  · have hsmall : T.card ≤ 1 := by omega
    have hchoose : T.card.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hzG : G = 0 := by
      funext e
      induction e using Sym2.ind with
      | h a b =>
        have hab : a = b := Subtype.ext
          (Finset.card_le_one_iff.mp hsmall a.property b.property)
        subst b
        exact hG a
    haveI : IsEmpty (Pair (Inside T)) := ⟨by
      intro p
      have hdg : p.val.IsDiag := by
        induction p.val using Sym2.ind with
        | h a b =>
          exact Subtype.ext (Finset.card_le_one_iff.mp hsmall a.property b.property)
      exact p.property (p.val.diagElem hdg) (Sym2.diag_diagElem hdg).symm⟩
    simp only [hchoose,Nat.cast_zero,mul_zero,zero_div]
    rw [(ThLean.W.S341.S3_37bStatement_holds V T hsmall).2 G]
    simp [hzG,indicator]

end ThLean.W.S340S

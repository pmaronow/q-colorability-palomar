module

public import ThLean.BP.S6.Foundation

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations

namespace ThLean.W.S602

open ThLean.BP.S6

private theorem uniformMean_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [Fintype.sum_equiv e _ _ (by intro a; rfl), Fintype.card_congr e]

private theorem uniformMean_prod_fst {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty B] (f : A → ℝ) :
    uniformMean (fun p : A × B => f p.1) = uniformMean f := by
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [Nat.cast_mul]
  field_simp [hB]

private theorem uniformMean_prod_fubini {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a, b))) := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  rw [← Finset.sum_div]
  simp only [Nat.cast_mul]
  field_simp

private theorem uniformMean_mul_left {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv]
  ring

private def pairNoDiagEquiv (n : ℕ) :
    Edge n ≃ {z : Sym2 (Fin n) // ¬ z.IsDiag} := by
  let noLoop_iff_not_isDiag (z : Sym2 (Fin n)) :
      (∀ v : Fin n, z ≠ s(v, v)) ↔ ¬ z.IsDiag := by
    induction z using Sym2.ind with
    | h a b => simp [eq_comm]
  exact
    { toFun := fun p => ⟨p.val, noLoop_iff_not_isDiag p.val |>.mp p.property⟩
      invFun := fun p => ⟨p.val, noLoop_iff_not_isDiag p.val |>.mpr p.property⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro p; cases p; rfl }

private theorem edge_card (n : ℕ) : Fintype.card (Edge n) = n.choose 2 := by
  calc
    Fintype.card (Edge n) = Fintype.card {z : Sym2 (Fin n) // ¬ z.IsDiag} :=
      Fintype.card_congr (pairNoDiagEquiv n)
    _ = (Fintype.card (Fin n)).choose 2 := Sym2.card_subtype_not_diag
    _ = n.choose 2 := by simp

private def splitHist {E : Type*} (m M : ℕ) (hm : m ≤ M) :
    (Fin M → E) ≃ ((Fin m → E) × (Fin (M - m) → E)) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le hm).symm) (Equiv.refl E)).trans
    (Fin.appendEquiv m (M - m)).symm

private theorem splitHist_fst {E : Type*} (m M : ℕ) (hm : m ≤ M)
    (x : Fin M → E) :
    (splitHist m M hm x).1 = fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hm⟩ := by
  funext i
  apply congrArg x
  apply Fin.ext
  simp

theorem S6_01bStatement_holds : S6_01bStatement := by
  intro n hn
  have hpair : 0 < Fintype.card (Edge n) := by
    rw [edge_card]
    exact Nat.choose_pos (by omega)
  haveI : Nonempty (Edge n) := Fintype.card_pos_iff.mp hpair
  constructor
  · intro m M hm F
    let e := splitHist (E := Edge n) m M hm
    calc
      uniformMean (fun x : Hist n M => F (takePrefix hm x)) =
          uniformMean (fun p : Hist n m × (Fin (M - m) → Edge n) => F p.1) := by
        have hfun : (fun x : Hist n M => F (takePrefix hm x)) =
            (fun p : Hist n m × (Fin (M - m) → Edge n) => F p.1) ∘ e := by
          funext x
          apply congrArg F
          exact (splitHist_fst m M hm x).symm
        rw [hfun]
        change uniformMean (fun x => F (e x).1) = _
        exact uniformMean_comp_equiv e (fun p => F p.1)
      _ = uniformMean F := uniformMean_prod_fst F
  · intro m J Z
    let e : Hist n (m + 1) ≃ Hist n m × Edge n :=
      Fin.succFunEquiv (Edge n) m
    calc
      uniformMean (fun x : Hist n (m + 1) =>
          J (takePrefix (Nat.le_succ m) x) *
            Z (takePrefix (Nat.le_succ m) x) (x ⟨m, Nat.lt_succ_self m⟩)) =
          uniformMean (fun p : Hist n m × Edge n => J p.1 * Z p.1 p.2) := by
        have hfun : (fun x : Hist n (m + 1) =>
            J (takePrefix (Nat.le_succ m) x) *
              Z (takePrefix (Nat.le_succ m) x) (x ⟨m, Nat.lt_succ_self m⟩)) =
            (fun p : Hist n m × Edge n => J p.1 * Z p.1 p.2) ∘ e := by
          funext x
          have hpref : takePrefix (Nat.le_succ m) x =
              fun i => x (Fin.castAdd 1 i) := by
            funext i
            congr 1
          have hlast : x ⟨m, Nat.lt_succ_self m⟩ = x (Fin.natAdd m 0) := by
            congr 1
          simp only [Function.comp_apply, e, Fin.succFunEquiv_apply]
          rw [hpref, hlast]
        rw [hfun]
        change uniformMean (fun x => J (e x).1 * Z (e x).1 (e x).2) = _
        exact uniformMean_comp_equiv e (fun p => J p.1 * Z p.1 p.2)
      _ = uniformMean (fun x : Hist n m => uniformMean (fun y : Edge n => J x * Z x y)) :=
          uniformMean_prod_fubini (fun p : Hist n m × Edge n => J p.1 * Z p.1 p.2)
      _ = uniformMean (fun x => J x * uniformMean (Z x)) := by
          congr 1
          funext x
          exact uniformMean_mul_left (J x) (Z x)

example : S6_01bStatement := S6_01bStatement_holds

end ThLean.W.S602

import ThLean.BP.S4.Finite

set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S4

namespace ThLean.W.S404

attribute [local instance] Classical.propDecidable

private lemma uniformMean_const_of_nonempty (A : Type) [Fintype A] [Nonempty A]
    (c : ℝ) : uniformMean (fun _ : A => c) = c := by
  simp [uniformMean]

private lemma uniformMean_zero_of_isEmpty (A : Type) [Fintype A] [IsEmpty A]
    (f : A → ℝ) : uniformMean f = 0 := by
  have hs : (∑ a : A, f a) = 0 := Finset.sum_eq_zero (fun a _ => isEmptyElim a)
  simp [uniformMean, hs]

private lemma variance_zero_of_unique (A : Type) [Fintype A] [Unique A]
    (f : A → ℝ) : variance f = 0 := by
  have hm : uniformMean f = f default := by simp [uniformMean]
  rw [variance, hm]
  have hsq : (fun a : A => (f a - f default) ^ 2) = fun _ => 0 := by
    funext a
    simp [Subsingleton.elim a default]
  rw [hsq]
  simp [uniformMean]

private lemma uniformMean_mono_of_nonempty (A : Type) [Fintype A] [Nonempty A]
    (f g : A → ℝ) (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  have hc : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›)
  apply (div_le_div_iff_of_pos_right hc).2
  exact Finset.sum_le_sum (fun a _ => h a)

private lemma uniformMean_prod_left (hFin : PreFiniteLawsStatement.{0,0})
    (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → ℝ) :
    uniformMean (fun p : A × B => f p.1) = uniformMean f := by
  calc
    uniformMean (fun p : A × B => f p.1) =
        uniformMean (fun a => uniformMean (fun b => f a)) := hFin.2.1 _ _ _
    _ = uniformMean f := by
      congr 1
      funext a
      exact uniformMean_const_of_nonempty B (f a)

private lemma variance_equiv (hFin : PreFiniteLawsStatement.{0,0})
    (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (f : B → ℝ) :
    variance (fun a => f (e a)) = variance f := by
  simp only [variance]
  have hm : uniformMean (fun a => f (e a)) = uniformMean f := hFin.1 _ _ e f
  rw [hm]
  exact hFin.1 _ _ e (fun b => (f b - uniformMean f) ^ 2)

private theorem tensorizeFin (hES : S4_ES_02Statement)
    (hFin : PreFiniteLawsStatement.{0,0}) (E : Type) [Fintype E] [Nonempty E]
    (n : ℕ) (f : (Fin n → E) → ℝ) :
    variance f ≤ ∑ i : Fin n, uniformMean (fun x : Fin n → E =>
      variance (fun a : E => f (Function.update x i a))) := by
  classical
  induction n with
  | zero =>
      simp [variance, uniformMean]
  | succ n ih =>
      let e : (Fin n → E) × E ≃ (Fin (n + 1) → E) :=
        { toFun := fun p => Fin.cons p.2 p.1
          invFun := fun x => (Fin.tail x, x 0)
          left_inv := by intro p; rcases p with ⟨t, a⟩; simp
          right_inv := by intro x; simp }
      let F (t : Fin n → E) : ℝ := uniformMean (fun a : E => f (Fin.cons a t))
      have hTail : Nonempty (Fin n → E) := ⟨fun _ => Classical.choice ‹Nonempty E›⟩
      letI : Nonempty (Fin n → E) := hTail
      have hdec := (hES (Fin n → E) E
        (fun p : (Fin n → E) × E => f (e p))).1
      have heq := variance_equiv hFin ((Fin n → E) × E)
        (Fin (n + 1) → E) e f
      have hdecomp : variance f =
          uniformMean (fun t : Fin n → E =>
            variance (fun a : E => f (Fin.cons a t))) + variance F := by
        calc
          variance f = variance (fun p : (Fin n → E) × E => f (e p)) := heq.symm
          _ = uniformMean (fun t : Fin n → E =>
                variance (fun a : E => f (Fin.cons a t))) + variance F := by
              simpa [e, F] using hdec
      have hzero :
          uniformMean (fun x : Fin (n + 1) → E =>
            variance (fun a : E => f (Function.update x 0 a))) =
          uniformMean (fun t : Fin n → E =>
            variance (fun a : E => f (Fin.cons a t))) := by
        have hr := hFin.1 _ _ e
          (fun x : Fin (n + 1) → E =>
            variance (fun a : E => f (Function.update x 0 a)))
        calc
          uniformMean (fun x : Fin (n + 1) → E =>
              variance (fun a : E => f (Function.update x 0 a))) =
              uniformMean (fun p : (Fin n → E) × E =>
                variance (fun a : E => f (Function.update (e p) 0 a))) := hr.symm
          _ = uniformMean (fun p : (Fin n → E) × E =>
                variance (fun a : E => f (Fin.cons a p.1))) := by
              congr 1
              funext p
              simp [e, Fin.update_cons_zero]
          _ = uniformMean (fun t : Fin n → E =>
                variance (fun a : E => f (Fin.cons a t))) :=
              uniformMean_prod_left hFin (Fin n → E) E
                (fun t => variance (fun a : E => f (Fin.cons a t)))
      have htail :
          (∑ j : Fin n, uniformMean (fun t : Fin n → E =>
            variance (fun b : E => F (Function.update t j b)))) ≤
          ∑ j : Fin n, uniformMean (fun x : Fin (n + 1) → E =>
            variance (fun b : E => f (Function.update x j.succ b))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hpoint (t : Fin n → E) :
            variance (fun b : E => F (Function.update t j b)) ≤
            uniformMean (fun a : E => variance (fun b : E =>
              f (Function.update (Fin.cons a t) j.succ b))) := by
          have hc := (hES E E
            (fun p : E × E => f (Fin.cons p.2 (Function.update t j p.1)))).2
          simpa [F, Fin.cons_update] using hc
        have hfub := hFin.2.1 (Fin n → E) E
          (fun p : (Fin n → E) × E => variance (fun b : E =>
            f (Function.update (Fin.cons p.2 p.1) j.succ b)))
        have hreindex := hFin.1 _ _ e
          (fun x : Fin (n + 1) → E => variance (fun b : E =>
            f (Function.update x j.succ b)))
        have hprod :
            uniformMean (fun t : Fin n → E => uniformMean (fun a : E =>
              variance (fun b : E =>
                f (Function.update (Fin.cons a t) j.succ b)))) =
            uniformMean (fun x : Fin (n + 1) → E => variance (fun b : E =>
              f (Function.update x j.succ b))) := by
          calc
            uniformMean (fun t : Fin n → E => uniformMean (fun a : E =>
                variance (fun b : E =>
                  f (Function.update (Fin.cons a t) j.succ b)))) =
                uniformMean (fun p : (Fin n → E) × E => variance (fun b : E =>
                  f (Function.update (Fin.cons p.2 p.1) j.succ b))) := hfub.symm
            _ = uniformMean (fun x : Fin (n + 1) → E => variance (fun b : E =>
                  f (Function.update x j.succ b))) := by
              calc
                uniformMean (fun p : (Fin n → E) × E => variance (fun b : E =>
                    f (Function.update (Fin.cons p.2 p.1) j.succ b))) =
                    uniformMean ((fun x : Fin (n + 1) → E => variance (fun b : E =>
                      f (Function.update x j.succ b))) ∘ e) := by
                  congr 1
                _ = uniformMean (fun x : Fin (n + 1) → E => variance (fun b : E =>
                    f (Function.update x j.succ b))) := hreindex
        calc
          uniformMean (fun t : Fin n → E =>
              variance (fun b : E => F (Function.update t j b))) ≤
              uniformMean (fun t : Fin n → E => uniformMean (fun a : E =>
                variance (fun b : E =>
                  f (Function.update (Fin.cons a t) j.succ b)))) :=
            uniformMean_mono_of_nonempty _ _ _ hpoint
          _ = uniformMean (fun x : Fin (n + 1) → E => variance (fun b : E =>
                f (Function.update x j.succ b))) := hprod
      rw [hdecomp, Fin.sum_univ_succ]
      exact add_le_add (le_of_eq hzero.symm) (ih F |>.trans htail)

private theorem tensorizeEquiv (hFin : PreFiniteLawsStatement.{0,0})
    {I J E : Type} [Fintype I] [Fintype J] [Fintype E]
    [DecidableEq I] [DecidableEq J]
    [Nonempty E] (e : I ≃ J) (f : (I → E) → ℝ)
    (hJ : ∀ g : (J → E) → ℝ,
      variance g ≤ ∑ j : J, uniformMean (fun y : J → E =>
        variance (fun a : E => g (Function.update y j a)))) :
    variance f ≤ ∑ i : I, uniformMean (fun x : I → E =>
      variance (fun a : E => f (Function.update x i a))) := by
  classical
  let eFun : (I → E) ≃ (J → E) :=
    { toFun := fun x j => x (e.symm j)
      invFun := fun y i => y (e i)
      left_inv := by intro x; funext i; simp
      right_inv := by intro y; funext j; simp }
  let g : (J → E) → ℝ := fun y => f (eFun.symm y)
  have hIne : Nonempty (I → E) := ⟨fun _ => Classical.choice ‹Nonempty E›⟩
  have hJne : Nonempty (J → E) := ⟨fun _ => Classical.choice ‹Nonempty E›⟩
  letI : Nonempty (I → E) := hIne
  letI : Nonempty (J → E) := hJne
  have hVar := variance_equiv hFin (J → E) (I → E) eFun.symm f
  have hTerm (j : J) :
      uniformMean (fun y : J → E => variance (fun a : E => g (Function.update y j a))) =
      uniformMean (fun x : I → E => variance (fun a : E =>
        f (Function.update x (e.symm j) a))) := by
    have hUpdate (y : J → E) (a : E) :
        eFun.symm (Function.update y j a) =
          Function.update (eFun.symm y) (e.symm j) a := by
      funext i
      by_cases hi : i = e.symm j
      · subst i
        simp [eFun]
      · have hej : e i ≠ j := by
          intro hij
          apply hi
          exact e.injective (by simpa using hij)
        simp [eFun, Function.update, hi, hej]
    calc
      uniformMean (fun y : J → E => variance (fun a : E => g (Function.update y j a))) =
          uniformMean (fun y : J → E => variance (fun a : E =>
            f (Function.update (eFun.symm y) (e.symm j) a))) := by
              congr 1
              funext y
              congr 1
              funext a
              simp [g, hUpdate]
      _ = uniformMean (fun x : I → E => variance (fun a : E =>
            f (Function.update x (e.symm j) a))) := by
          let q : (I → E) → ℝ := fun x => variance (fun a : E =>
            f (Function.update x (e.symm j) a))
          have hm := hFin.1 (J → E) (I → E) eFun.symm q
          simpa [q, Function.comp_def] using hm
  have hsum :
      (∑ j : J, uniformMean (fun y : J → E => variance (fun a : E =>
        g (Function.update y j a)))) =
      (∑ i : I, uniformMean (fun x : I → E => variance (fun a : E =>
        f (Function.update x i a)))) := by
    symm
    exact Fintype.sum_equiv e _ _ (fun i => by simpa using (hTerm (e i)).symm)
  calc
    variance f = variance g := hVar.symm
    _ ≤ ∑ j : J, uniformMean (fun y : J → E =>
          variance (fun a : E => g (Function.update y j a))) := hJ g
    _ = ∑ i : I, uniformMean (fun x : I → E =>
          variance (fun a : E => f (Function.update x i a))) := hsum

theorem S4_ES_03Statement_of_deps
    (hES : S4_ES_02Statement)
    (hFin : PreFiniteLawsStatement.{0,0}) : S4_ES_03Statement := by
  classical
  intro I E instI instDecEq instE f
  by_cases hE : Nonempty E
  · letI : Nonempty E := hE
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    have hJ : ∀ g : (Fin (Fintype.card I) → E) → ℝ,
        variance g ≤ ∑ j : Fin (Fintype.card I), uniformMean (fun y : Fin (Fintype.card I) → E =>
          variance (fun a : E => g (Function.update y j a))) := by
      intro g
      exact tensorizeFin hES hFin E (Fintype.card I) g
    exact tensorizeEquiv hFin e f hJ
  · by_cases hIndex : Nonempty I
    · letI : IsEmpty E := ⟨fun a => hE ⟨a⟩⟩
      letI : IsEmpty (I → E) := ⟨fun x => hE ⟨x (Classical.choice hIndex)⟩⟩
      have hv : variance f = 0 := by
        rw [variance, uniformMean_zero_of_isEmpty _ f]
        exact uniformMean_zero_of_isEmpty _ _
      have hs :
          (∑ i : I, uniformMean (fun x : I → E =>
            variance (fun a : E => f (Function.update x i a)))) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact uniformMean_zero_of_isEmpty _ _
      rw [hv, hs]
    · letI : Unique (I → E) :=
        { default := fun i => (hIndex ⟨i⟩).elim
          uniq := fun x => by
            funext i
            exact (hIndex ⟨i⟩).elim }
      letI : IsEmpty I := ⟨fun i => hIndex ⟨i⟩⟩
      have hv : variance f = 0 := variance_zero_of_unique _ f
      have hs :
          (∑ i : I, uniformMean (fun x : I → E =>
            variance (fun a : E => f (Function.update x i a)))) = 0 := by
        simp
      rw [hv, hs]

end ThLean.W.S404

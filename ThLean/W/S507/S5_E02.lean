module

public import ThLean.BP.S5.Elementary

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S507

open ThLean.BP.S5
open ThresholdFoundations

private theorem wordFiberCard_reindex
    {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (c : B → ℕ) :
    wordFiberCard (fun a => c (e a)) = wordFiberCard c := by
  classical
  unfold wordFiberCard
  rw [Equiv.sum_comp e c]
  apply Fintype.card_congr
  let w : (Fin (∑ b, c b) → A) ≃ (Fin (∑ b, c b) → B) :=
    { toFun := fun x i => e (x i)
      invFun := fun x i => e.symm (x i)
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp }
  apply Equiv.subtypeEquiv w
  intro x
  constructor
  · intro hx b
    have hfilter :
        Finset.univ.filter (fun i => w x i = b) =
          Finset.univ.filter (fun i => x i = e.symm b) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (e (x i) = b) ↔ (x i = e.symm b)
      constructor
      · intro hi
        apply e.injective
        simpa using hi
      · intro hi
        rw [hi]
        simp
    rw [hfilter]
    simpa using hx (e.symm b)
  · intro hx a
    have hfilter :
        Finset.univ.filter (fun i => x i = a) =
          Finset.univ.filter (fun i => w x i = e a) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (x i = a) ↔ (e (x i) = e a)
      constructor
      · intro hi
        rw [hi]
      · intro hi
        exact e.injective hi
    rw [hfilter]
    exact hx (e a)

private theorem multinomial_word_fiber (hA : S5_E02AStatement) :
    ∀ (E : Type) [Fintype E] (c : E → ℕ),
      wordFiberCard c * ∏ e, (c e).factorial = (∑ e, c e).factorial := by
  classical
  let P : (E : Type) → [Fintype E] → Prop := fun E _ =>
    ∀ c : E → ℕ,
      wordFiberCard c * ∏ e, (c e).factorial = (∑ e, c e).factorial
  have hP : ∀ E : Type, ∀ [Fintype E], P E := by
    intro E inst
    refine Fintype.induction_empty_option
      (P := P)
      (of_equiv := ?_)
      (h_empty := ?_)
      (h_option := ?_)
      E
    · intro A B _ e ih c
      letI : Fintype A := Fintype.ofEquiv B e.symm
      calc
        wordFiberCard c * ∏ b, (c b).factorial =
            wordFiberCard (fun a => c (e a)) *
              ∏ a, (c (e a)).factorial := by
                rw [← wordFiberCard_reindex e c,
                  ← Equiv.prod_comp e (fun b => (c b).factorial)]
        _ = (∑ a, c (e a)).factorial := ih (fun a => c (e a))
        _ = (∑ b, c b).factorial := by rw [Equiv.sum_comp e c]
    · intro c
      simp [wordFiberCard]
    · intro E _ ih c
      letI : DecidablePred (fun v : Option E => v ≠ none) :=
        fun v => @instDecidableNot (v = none) (Classical.propDecidable (v = none))
      let c' : E → ℕ := fun a => c (some a)
      let S := {v : Option E // v ≠ none}
      let e : E ≃ S :=
        { toFun := fun a => ⟨some a, by simp⟩
          invFun := fun v =>
            match v with
            | ⟨none, hn⟩ => False.elim (hn rfl)
            | ⟨some a, _⟩ => a
          left_inv := by intro a; rfl
          right_inv := by
            intro v
            rcases v with ⟨v, hv⟩
            cases v with
            | none => exact (hv rfl).elim
            | some a => rfl }
      let r : ℕ := ∑ a : E, c' a
      have hrec := hA (Option E) c none
      have hrest : wordFiberCard (fun v : S => c v.val) = wordFiberCard c' := by
        simpa [c', S, e] using
          (wordFiberCard_reindex e (fun v : S => c v.val)).symm
      have hIH : wordFiberCard c' * ∏ a : E, (c' a).factorial = r.factorial := by
        simpa [P, r] using ih c'
      have htotal : (∑ v : Option E, c v) = c none + r := by
        simp [r, c', Fintype.sum_option]
      calc
        wordFiberCard c * ∏ v, (c v).factorial =
            ((∑ v : Option E, c v).choose (c none) *
              wordFiberCard (fun v : S => c v.val)) *
              ((c none).factorial * ∏ a : E, (c' a).factorial) := by
                rw [hrec, Fintype.prod_option]
        _ = ((∑ v : Option E, c v).choose (c none) * (c none).factorial) *
              (wordFiberCard c' * ∏ a : E, (c' a).factorial) := by
                rw [hrest]
                ac_rfl
        _ = ((c none + r).choose (c none) * (c none).factorial) * r.factorial := by
              rw [htotal, hIH]
        _ = (∑ v : Option E, c v).factorial := by
              rw [htotal]
              simpa [Nat.add_sub_cancel_left] using
                (Nat.choose_mul_factorial_mul_factorial
                  (n := c none + r) (k := c none) (Nat.le_add_right _ _))
  intro E inst c
  exact hP E c

/-- The multinomial identity and uniform histogram probability, assuming the one-letter
position-counting recurrence S5_E02A. -/
theorem S5_E02Statement_of_deps (hA : S5_E02AStatement) : S5_E02Statement := by
  classical
  have hmult := multinomial_word_fiber hA
  constructor
  · exact hmult
  · intro E inst hne c
    let n : ℕ := ∑ e, c e
    let hist : (Fin n → E) → Prop := fun x =>
      ∀ e, (Finset.univ.filter (fun i => x i = e)).card = c e
    have hcount := hmult E c
    have hcard : 0 < Fintype.card E := Fintype.card_pos_iff.mpr hne
    have hbase : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcard)
    have hpow : (Fintype.card E : ℝ)^n ≠ 0 := pow_ne_zero _ hbase
    have hfac : (∏ e, ((c e).factorial : ℝ)) ≠ 0 := by positivity
    have hcountR : (wordFiberCard c : ℝ) * ∏ e, ((c e).factorial : ℝ) =
        (n.factorial : ℝ) := by
      dsimp [n] at hcount ⊢
      exact_mod_cast hcount
    have hprob : uniformProb hist =
        (wordFiberCard c : ℝ) / (Fintype.card E : ℝ)^n := by
      letI : DecidablePred hist := fun x => Classical.propDecidable (hist x)
      simp only [uniformProb, uniformMean]
      have hsum :
          (∑ x : Fin n → E, indicator (hist x)) =
            (Fintype.card {x : Fin n → E // hist x} : ℝ) := by
        simp [indicator, Finset.sum_boole, Fintype.card_subtype]
      have hsub :
          Fintype.card {x : Fin n → E // hist x} = (Finset.univ.filter hist).card := by
        exact Fintype.card_subtype hist
      have hword :
          wordFiberCard c = (Finset.univ.filter hist).card := by
        simp [wordFiberCard, hist, n, Fintype.card_subtype]
      calc
        (∑ x : Fin n → E, indicator (hist x)) /
            (Fintype.card (Fin n → E) : ℝ) =
              (Fintype.card {x : Fin n → E // hist x} : ℝ) /
                (Fintype.card (Fin n → E) : ℝ) := by
                  exact congrArg (fun z : ℝ => z / (Fintype.card (Fin n → E) : ℝ)) hsum
        _ = (wordFiberCard c : ℝ) / (Fintype.card E : ℝ)^n := by
              have hcardeq :
                  Fintype.card {x : Fin n → E // hist x} = wordFiberCard c :=
                hsub.trans hword.symm
              rw [hcardeq]
              simp [Fintype.card_fun]
    calc
      uniformProb hist = (wordFiberCard c : ℝ) / (Fintype.card E : ℝ)^n := hprob
      _ = (n.factorial : ℝ) /
            ((Fintype.card E : ℝ)^n * ∏ e, ((c e).factorial : ℝ)) := by
              rw [← hcountR]
              field_simp [hpow, hfac]
      _ = ((∑ e, c e).factorial : ℝ) /
            ((Fintype.card E : ℝ)^(∑ e, c e) *
              ∏ e, ((c e).factorial : ℝ)) := by rfl

end ThLean.W.S507

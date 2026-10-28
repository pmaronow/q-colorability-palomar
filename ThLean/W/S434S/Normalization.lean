import ThLean.W.S434.S4_BRIDGE_01C

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S434S
open ThresholdFoundations ThLean.BP.S4

private theorem uniformMean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [Equiv.sum_comp e, Fintype.card_congr e]

private theorem uniformMean_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a, b))) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div]
  rw [mul_comm, div_mul_eq_div_div]

private theorem uniformMean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := A)
  simp [uniformMean, hA]

private theorem uniformMean_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp only [uniformMean, Finset.sum_sub_distrib, sub_div]

private theorem tupleGraph_snoc {V : Type*} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (e : Pair V) :
    tupleGraph (Fin.snoc x e) = addPair (tupleGraph x) e := by
  ext d
  simp only [tupleGraph, addPair, addEdge, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  by_cases hd : d = e.val
  · subst d
    simp only [Function.update_self, ite_true]
  · rw [Function.update_of_ne hd]
    simp only [ite_eq_right (Ne.symm hd), add_zero, tupleGraph, Finset.card_filter]

private theorem colorable_of_addPair {V : Type*} {q : ℕ}
    (G : MGraph V) (e : Pair V) : Colorable q (addPair G e) → Colorable q G := by
  rintro ⟨σ, hσ⟩
  refine ⟨σ, fun u v huv => hσ u v (lt_of_lt_of_le huv ?_)⟩
  by_cases h : s(u, v) = e.val
  · simp [addPair, addEdge, h]
  · simp [addPair, addEdge, Function.update_of_ne h]

private theorem indicator_sub {P Q : Prop} (h : Q → P) :
    indicator P - indicator Q = indicator (P ∧ ¬ Q) := by
  by_cases hp : P
  · by_cases hq : Q <;> simp [indicator, hp, hq]
  · have hq : ¬ Q := fun hq => hp (h hq)
    simp [indicator, hp, hq]

private theorem uniformMean_snoc {V : Type*} [Fintype V] {m : ℕ}
    (f : EdgeTuple V (m+1) → ℝ) :
    uniformMean f = uniformMean (fun x : EdgeTuple V m =>
      uniformMean (fun e : Pair V => f (Fin.snoc x e))) := by
  let e : EdgeTuple V m × Pair V ≃ EdgeTuple V (m+1) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (m+1) => Pair V))
  rw [← uniformMean_equiv e f, uniformMean_prod]
  rfl

/-- The mass of one terminal step is the loss of survival at that step. -/
theorem terminalStep_one_eq {V : Type*} [Fintype V] [Nonempty (Pair V)]
    (q m : ℕ) : terminalStep (V := V) q m (fun _ _ => 1) =
      processSurvival (V := V) q m - processSurvival (V := V) q (m+1) := by
  have hnext : processSurvival (V := V) q (m+1) =
      uniformMean (fun x : EdgeTuple V m => uniformMean (fun e : Pair V =>
        indicator (Colorable q (addPair (tupleGraph x) e)))) := by
    unfold processSurvival survival uniformProb
    simp only [zero_add]
    rw [uniformMean_snoc]
    simp_rw [tupleGraph_snoc]
  rw [hnext]
  unfold terminalStep processSurvival survival uniformProb
  simp only [zero_add]
  rw [← uniformMean_sub]
  apply congrArg uniformMean
  funext x
  rw [← uniformMean_const (A := Pair V) (indicator (Colorable q (tupleGraph x))),
    ← uniformMean_sub]
  apply congrArg uniformMean
  funext e
  rw [indicator_sub (colorable_of_addPair (tupleGraph x) e)]
  by_cases hf : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
  · simp [indicator, hf]
  · simp [indicator, hf]

private theorem uniformProb_bounds {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    0 ≤ uniformProb P ∧ uniformProb P ≤ 1 := by
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := A)
  constructor
  · unfold uniformProb uniformMean
    apply div_nonneg _ hcard.le
    apply Finset.sum_nonneg
    intro a ha
    by_cases h : P a <;> simp [indicator, h]
  · unfold uniformProb uniformMean
    rw [div_le_iff₀ hcard, one_mul]
    calc
      (∑ a : A, indicator (P a)) ≤ ∑ _ : A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases h : P a <;> simp [indicator, h]
      _ = Fintype.card A := by simp

/-- A finite interval of terminal transitions has total mass at most one. -/
theorem terminalProb_true_le_one {V : Type} [Fintype V] [Nonempty (Pair V)]
    (q L U : ℕ) (hLU : L ≤ U) :
    terminalProb (V := V) q L U (fun _ _ => True) ≤ 1 := by
  have hsum : terminalProb (V := V) q L U (fun _ _ => True) =
      processSurvival (V := V) q L - processSurvival (V := V) q U := by
    calc
      terminalProb (V := V) q L U (fun _ _ => True) =
          ∑ m ∈ Finset.Ico L U, terminalStep (V := V) q m (fun _ _ => 1) := by
            simp only [terminalProb, terminalReal, terminalStep, indicator, ite_true]
      _ = ∑ m ∈ Finset.Ico L U,
          (processSurvival (V := V) q m - processSurvival (V := V) q (m+1)) := by
            simp_rw [terminalStep_one_eq]
      _ = processSurvival (V := V) q L - processSurvival (V := V) q U := by
        have ht := Finset.sum_Ico_sub (fun m => -processSurvival (V := V) q m) hLU
        simpa only [neg_sub_neg, neg_sub] using ht
  rw [hsum]
  have hL := (uniformProb_bounds
    (fun x : EdgeTuple V L => Colorable q ((0 : MGraph V) + tupleGraph x))).2
  have hU := (uniformProb_bounds
    (fun x : EdgeTuple V U => Colorable q ((0 : MGraph V) + tupleGraph x))).1
  change processSurvival (V := V) q L ≤ 1 at hL
  change 0 ≤ processSurvival (V := V) q U at hU
  linarith

end ThLean.W.S434S

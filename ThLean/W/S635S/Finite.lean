import ThLean.BP.S6.Descent
import ThLean.W.S601.FiniteMean
import ThLean.W.S602.Foundation
import ThLean.W.S306.Graph

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S635S

lemma edge_nonempty {n : ℕ} (hn : 3 ≤ n) : Nonempty (Edge n) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  exact ⟨⟨s(a, b), by simp [a, b]⟩⟩

lemma mean_nonneg {A : Type} [Fintype A] (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ uniformMean f :=
  (ThLean.W.S601.S6_01aStatement_holds A).nonneg f hf

lemma mean_sub {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_sub_distrib, sub_div]

lemma meanENN_ofReal {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    uniformMeanENN (fun a => ENNReal.ofReal (f a)) =
      ENNReal.ofReal (uniformMean f) := by
  have hc : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  simp [uniformMeanENN, uniformMean, ENNReal.ofReal_div_of_pos hc,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a)]

lemma mean_congr {A : Type} (i j : Fintype A) {f g : A → ℝ}
    (h : ∀ a, f a = g a) : @uniformMean A i f = @uniformMean A j g := by
  have hij : i = j := Subsingleton.elim _ _
  subst j
  exact congrArg (@uniformMean A i) (funext h)

lemma meanENN_ofReal_congr {A : Type} [Nonempty A] (i j : Fintype A)
    {f : A → ℝ≥0∞} {g : A → ℝ} (h : ∀ a, f a = ENNReal.ofReal (g a))
    (hg : ∀ a, 0 ≤ g a) :
    @uniformMeanENN A i f = ENNReal.ofReal (@uniformMean A j g) := by
  have hij : i = j := Subsingleton.elim _ _
  subst j
  rw [show f = (fun a => ENNReal.ofReal (g a)) from funext h]
  exact @meanENN_ofReal A i _ g hg

lemma killing_iff {n q : ℕ} (hn : 3 ≤ n) (hq : 3 ≤ q)
    (G : Graph n) (e : Edge n) :
    FrozenPair q G e ↔ Colorable q G ∧ ¬ Colorable q (addPair G e) := by
  have ha := (ThLean.W.S306.S3_10Statement_holds
    (Fin n) q (by omega) (by simp; omega)).1 G e
  have hc : FrozenPair q G e → Colorable q G := by
    rintro ⟨u, v, _, hf⟩
    exact hf.1
  tauto

lemma prefix_mono {n M q : ℕ} (x : Hist n M) {a b : ℕ} (hab : a ≤ b)
    (hb : Colorable q (tuplePrefix x b)) : Colorable q (tuplePrefix x a) := by
  obtain ⟨σ, hσ⟩ := hb
  refine ⟨σ, fun u v huv => hσ u v (lt_of_lt_of_le huv ?_)⟩
  unfold tuplePrefix
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1.trans_le hab, hi.2⟩

lemma prefix_full {n M : ℕ} (x : Hist n M) : tuplePrefix x M = tupleGraph x := by
  funext e
  simp [tuplePrefix, tupleGraph]

lemma prefix_zero {n M : ℕ} (x : Hist n M) : tuplePrefix x 0 = 0 := by
  funext e
  simp [tuplePrefix]

lemma colorable_zero {n q : ℕ} (hq : 3 ≤ q) : Colorable q (0 : Graph n) := by
  refine ⟨fun _ => ⟨0, by omega⟩, ?_⟩
  intro u v huv
  simp at huv

lemma graph_takePrefix {n m M : ℕ} (hm : m ≤ M) (x : Hist n M) :
    tupleGraph (takePrefix hm x) = tuplePrefix x m := by
  classical
  letI : DecidableEq (Fin n) := Classical.decEq _
  funext e
  unfold tupleGraph tuplePrefix
  refine Finset.card_bij
    (fun i _ => (⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩ : Fin M)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨i.isLt, hi⟩
  · intro a _ b _ h
    exact Fin.ext (congrArg (fun z : Fin M => z.val) h)
  · intro b hb
    have hb' := (Finset.mem_filter.mp hb).2
    refine ⟨⟨b.val, hb'.1⟩, ?_, Fin.ext rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb'.2

lemma graph_succ {n m : ℕ} (x : Hist n (m + 1)) :
    tupleGraph x = addPair (tupleGraph (takePrefix (Nat.le_succ m) x))
      (x ⟨m, Nat.lt_succ_self m⟩) := by
  classical
  letI : DecidableEq (Fin n) := Classical.decEq _
  funext e
  unfold tupleGraph addPair addEdge
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  by_cases he : e = (x ⟨m, Nat.lt_succ_self m⟩).val
  all_goals
    simp [Function.update, he, eq_comm, takePrefix, Fin.last, Fin.castSucc]
    simp only [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    have hi : Fin.castAdd 1 i = (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m+1)) :=
      Fin.ext rfl
    rw [hi] <;> simp only [eq_comm]

lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split_ifs <;> norm_num

lemma indicator_transition (P Q : Prop) (h : Q → P) :
    indicator (P ∧ ¬ Q) = indicator P - indicator Q := by
  by_cases hp : P <;> by_cases hq : Q <;> simp_all [indicator]

lemma terminalStep_eq {n q : ℕ} (hn : 3 ≤ n) (hq : 3 ≤ q) (m : ℕ)
    (A : Graph n → Edge n → Prop) :
    terminalStepENN q m (fun G e => if A G e then 1 else 0) =
      ENNReal.ofReal (meanGraph m (kappaKind q A)) := by
  letI : Nonempty (Edge n) := edge_nonempty hn
  have hi (G : Graph n) (i : Fintype (Edge n)) :
      @uniformMeanENN (Edge n) i (fun e : Edge n =>
        if Colorable q G ∧ ¬ Colorable q (addPair G e)
        then (if A G e then 1 else 0) else 0) =
      ENNReal.ofReal (kappaKind q A G) := by
    unfold kappaKind uniformProb
    apply meanENN_ofReal_congr
    · intro e
      simp only [← killing_iff hn hq G e]
      by_cases hf : FrozenPair q G e <;> by_cases ha : A G e <;>
        simp [indicator, hf, ha]
    · exact fun e => indicator_nonneg _
  unfold terminalStepENN meanGraph
  apply meanENN_ofReal_congr
  · intro x
    exact hi (tupleGraph x) _
  · intro x
    unfold kappaKind uniformProb uniformMean
    apply div_nonneg
    · exact Finset.sum_nonneg (fun e _ => indicator_nonneg _)
    · exact Nat.cast_nonneg _

lemma hazard_difference {n q : ℕ} (hn : 3 ≤ n) (hq : 3 ≤ q) (m : ℕ) :
    meanGraph (n := n) m (kappa q) =
      uniformProb (fun x : Hist n m => Colorable q (tupleGraph x)) -
      uniformProb (fun x : Hist n (m+1) => Colorable q (tupleGraph x)) := by
  have havg :
      uniformMean (fun x : Hist n (m+1) =>
        indicator (FrozenPair q (tupleGraph (takePrefix (Nat.le_succ m) x))
          (x ⟨m, Nat.lt_succ_self m⟩))) = meanGraph (n := n) m (kappa q) := by
    calc
      _ = uniformMean (fun x : Hist n m => uniformMean (fun e : Edge n =>
          indicator (FrozenPair q (tupleGraph x) e))) := by
        simpa only [one_mul] using
          (ThLean.W.S602.S6_01bStatement_holds n hn).2 m (fun _ => 1)
            (fun x e => indicator (FrozenPair q (tupleGraph x) e))
      _ = _ := by
        unfold meanGraph kappa uniformProb
        apply mean_congr
        intro x
        exact mean_congr _ _ (fun _ => rfl)
  have hp (x : Hist n (m+1)) :
      indicator (FrozenPair q (tupleGraph (takePrefix (Nat.le_succ m) x))
          (x ⟨m, Nat.lt_succ_self m⟩)) =
        indicator (Colorable q (tupleGraph (takePrefix (Nat.le_succ m) x))) -
        indicator (Colorable q (tupleGraph x)) := by
    rw [killing_iff hn hq, graph_succ x]
    apply indicator_transition
    intro hc
    exact ((ThLean.W.S306.S3_10Statement_holds
      (Fin n) q (by omega) (by simp; omega)).1 _ _).1 hc |>.1
  calc
    _ = uniformMean (fun x : Hist n (m+1) =>
          indicator (FrozenPair q (tupleGraph (takePrefix (Nat.le_succ m) x))
            (x ⟨m, Nat.lt_succ_self m⟩))) := havg.symm
    _ = uniformMean (fun x : Hist n (m+1) =>
          indicator (Colorable q (tupleGraph (takePrefix (Nat.le_succ m) x))) -
          indicator (Colorable q (tupleGraph x))) := congrArg uniformMean (funext hp)
    _ = _ := by
      rw [mean_sub, (ThLean.W.S602.S6_01bStatement_holds n hn).1 m (m+1)
        (Nat.le_succ m) (fun x => indicator (Colorable q (tupleGraph x)))]
      rfl

end ThLean.W.S635S

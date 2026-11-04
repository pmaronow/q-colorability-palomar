module

public import ThLean.W.S635S.Finite

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S635S

lemma survival_zero {n q : ℕ} (hn : 3 ≤ n) (hq : 3 ≤ q) :
    uniformProb (fun x : Hist n 0 => Colorable q (tupleGraph x)) = 1 := by
  letI : Nonempty (Edge n) := edge_nonempty hn
  have hg (x : Hist n 0) : tupleGraph x = 0 := by
    funext e
    simp [tupleGraph]
  have hi : (fun x : Hist n 0 => indicator (Colorable q (tupleGraph x))) =
      (fun _ => (1 : ℝ)) := by
    funext x
    simp [hg x, indicator, colorable_zero hq]
  unfold uniformProb
  rw [hi]
  exact (ThLean.W.S601.S6_01aStatement_holds (Hist n 0)).const Fintype.card_pos 1

lemma hazard_sum {n q : ℕ} (hn : 3 ≤ n) (hq : 3 ≤ q) (M : ℕ) :
    (∑ m ∈ Finset.range M, meanGraph (n := n) m (kappa q)) =
      1 - uniformProb (fun x : Hist n M => Colorable q (tupleGraph x)) := by
  induction M with
  | zero => simp [survival_zero hn hq]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, hazard_difference hn hq]
    ring

lemma capped_event_iff {n q M : ℕ} (hq : 3 ≤ q) (x : Hist n M) :
    cappedLast q x < M ↔ ¬ Colorable q (tupleGraph x) := by
  constructor
  · intro hcap hcol
    have hp (k : ℕ) (hk : k ∈ Finset.range M) :
        Colorable q (tuplePrefix x (k+1)) := by
      apply prefix_mono x (a := k+1) (b := M)
      · have := Finset.mem_range.mp hk
        omega
      · rwa [prefix_full]
    have heq : cappedLast q x = M := by
      unfold cappedLast
      calc
        _ = ∑ _k ∈ Finset.range M, (1 : ℕ) :=
          Finset.sum_congr rfl (fun k hk => if_pos (hp k hk))
        _ = M := by simp
    omega
  · intro hbad
    have hM : 0 < M := by
      by_contra h
      have hzero : M = 0 := by omega
      apply hbad
      have hg : tupleGraph x = 0 := by
        exact (prefix_full x).symm.trans
          ((congrArg (tuplePrefix x) hzero).trans (prefix_zero x))
      rw [hg]
      exact colorable_zero hq
    have hlast : ¬ Colorable q (tuplePrefix x (M-1+1)) := by
      have htime : M-1+1 = M := by omega
      simpa only [htime, prefix_full] using hbad
    unfold cappedLast
    calc
      _ < ∑ _k ∈ Finset.range M, (1 : ℕ) := by
        apply Finset.sum_lt_sum
        · intro k _
          split_ifs <;> omega
        · refine ⟨M-1, Finset.mem_range.mpr (by omega), ?_⟩
          simp [hlast]
      _ = M := by simp

lemma prob_complement {A : Type} [Fintype A] [Nonempty A] (P : A → Prop) :
    uniformProb (fun a => ¬ P a) = 1 - uniformProb P := by
  have hi (a : A) : indicator (¬ P a) = 1 - indicator (P a) := by
    by_cases ha : P a <;> simp [indicator, ha]
  unfold uniformProb
  rw [show (fun a => indicator (¬ P a)) = (fun a => 1 - indicator (P a))
    from funext hi, mean_sub]
  rw [(ThLean.W.S601.S6_01aStatement_holds A).const Fintype.card_pos 1]

lemma kindMean_nonneg {n q m : ℕ} (A : Graph n → Edge n → Prop) :
    0 ≤ meanGraph m (kappaKind q A) := by
  unfold meanGraph kappaKind uniformProb uniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro x _
    apply div_nonneg
    · exact Finset.sum_nonneg (fun e _ => indicator_nonneg _)
    · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

/-- The finite terminal bridge and exact total hazard identity. -/
theorem S6_32aStatement_holds : ThLean.BP.S6.S6_32aStatement := by
  intro n q M D hn hq
  letI : Nonempty (Edge n) := edge_nonempty hn
  refine ⟨?_, ?_, ?_⟩
  · unfold highTerminalProbability
    simp_rw [terminalStep_eq hn hq]
    rw [ENNReal.toReal_sum (fun m _ => ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro m _
    exact ENNReal.toReal_ofReal (kindMean_nonneg _)
  · rw [hazard_sum hn hq]
    have hnonneg := (ThLean.W.S601.S6_01aStatement_holds (Hist n M)).prob
      (fun x => Colorable q (tupleGraph x)) |>.1
    linarith
  · rw [hazard_sum hn hq]
    have hevent : (fun x : Hist n M => cappedLast q x < M) =
        (fun x : Hist n M => ¬ Colorable q (tupleGraph x)) :=
      funext (fun x => propext (capped_event_iff hq x))
    rw [hevent, prob_complement]

example : ThLean.BP.S6.S6_32aStatement := S6_32aStatement_holds

end ThLean.W.S635S

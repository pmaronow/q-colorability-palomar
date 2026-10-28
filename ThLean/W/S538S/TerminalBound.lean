import ThLean.W.S538S.FiniteMean
import ThLean.W.S553.S5_11

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S538S
open ThresholdFoundations

lemma terminal_frozen {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V)
    (e : Pair V) (hd : Colorable q G ∧ ¬ Colorable q (addPair G e)) :
    FrozenPair q G e := by
  have he : e.val = s(e.val.out.1, e.val.out.2) := (Quot.out_eq e.val).symm
  refine ⟨e.val.out.1, e.val.out.2, he, hd.1, ?_⟩
  intro σ hσ
  by_contra hne
  apply hd.2
  refine ⟨σ, ?_⟩
  intro u v huv
  by_cases huv' : s(u, v) = e.val
  · rcases Sym2.eq_iff.mp (huv'.trans he) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact fun hEq => hne hEq.symm
  · apply hσ u v
    simpa [addPair, addEdge, huv'] using huv

lemma kappa_nonneg {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V) :
    0 ≤ kappa q G := by
  apply uniformMean_nonneg
  intro e
  unfold indicator
  split_ifs <;> norm_num

lemma terminalStepENN_le_hazard {V : Type*} [Fintype V] (q m : ℕ)
    (h : MGraph V → Pair V → ℝ≥0∞) (hh : ∀ G e, h G e ≤ 1) :
    terminalStepENN q m h ≤ ENNReal.ofReal (graphMean m (kappa (V := V) q)) := by
  have hk (G : MGraph V) :
      uniformMeanENN (fun e : Pair V => if FrozenPair q G e then 1 else 0) =
        ENNReal.ofReal (kappa q G) := by
    simpa only [kappa, uniformProb, ofReal_indicator] using
      uniformMeanENN_ofReal (fun e : Pair V => indicator (FrozenPair q G e))
        (fun e => by unfold indicator; split_ifs <;> norm_num)
  unfold terminalStepENN
  calc
    _ ≤ uniformMeanENN (fun x : EdgeTuple V m =>
        uniformMeanENN (fun e : Pair V => if FrozenPair q (tupleGraph x) e then 1 else 0)) := by
      apply uniformMeanENN_mono
      intro x
      apply uniformMeanENN_mono
      intro e
      by_cases hd : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
      · simpa only [ite_eq_left hd, ite_eq_left (terminal_frozen q _ e hd)] using hh (tupleGraph x) e
      · simp [hd]
    _ = ENNReal.ofReal (graphMean m (kappa (V := V) q)) := by
      simp_rw [hk]
      exact uniformMeanENN_ofReal _ (fun x => kappa_nonneg q (tupleGraph x))

/-- The sum of all finite terminal cylinders has mass at most one. -/
theorem terminalMeanENN_le_one {V : Type} [Fintype V] (q : ℕ)
    (hq : 3 ≤ q) (hV : 2 ≤ Fintype.card V)
    (h : MGraph V → Pair V → ℝ≥0∞) (hh : ∀ G e, h G e ≤ 1) :
    terminalMeanENN q h ≤ 1 := by
  let a : ℕ → ℝ := fun m => graphMean m (kappa (V := V) q)
  have ha (m : ℕ) : 0 ≤ a m :=
    uniformMean_nonneg _ (fun x => kappa_nonneg q (tupleGraph x))
  have hinc (m : ℕ) : a m = hittingMass (V := V) q m :=
    ThLean.W.S553.S5_11HazardIncrementStatement_holds V q hq hV m
  have hs0 : processSurvival (V := V) q 0 = 1 := by
    have hg (x : EdgeTuple V 0) : tupleGraph x = 0 := by
      ext e
      simp [tupleGraph]
    have hc (x : EdgeTuple V 0) : Colorable q (tupleGraph x) := by
      rw [hg]
      refine ⟨fun _ => (⟨0, by omega⟩ : Fin q), ?_⟩
      intro u v he
      simp at he
    simp [processSurvival, survival, uniformProb, uniformMean, indicator, hc]
  have hs (m : ℕ) : 0 ≤ processSurvival (V := V) q m := by
    apply uniformMean_nonneg
    intro x
    unfold indicator
    split_ifs <;> norm_num
  have htel (M : ℕ) :
      (∑ m ∈ Finset.range M, a m) = 1 - processSurvival (V := V) q M := by
    induction M with
    | zero => simp [hs0]
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, hinc, hittingMass]
      ring
  unfold terminalMeanENN
  calc
    _ ≤ ∑' m, ENNReal.ofReal (a m) :=
      ENNReal.tsum_le_tsum (fun m => terminalStepENN_le_hazard q m h hh)
    _ ≤ 1 := by
      apply ENNReal.tsum_le_of_sum_range_le
      intro M
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => ha m), htel]
      simpa using ENNReal.ofReal_le_ofReal (sub_le_self (1 : ℝ) (hs M))

end ThLean.W.S538S

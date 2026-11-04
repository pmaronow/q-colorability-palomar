module

public import ThLean.W.S538S.TerminalBound

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S538S
open ThresholdFoundations

/-- Restricting terminal events to finitely many times can only decrease their probability. -/
theorem terminalWindowProbability_le {V : Type} [Fintype V] (q : ℕ)
    (hq : 3 ≤ q) (hV : 2 ≤ Fintype.card V)
    (A : MGraph V → Pair V → Prop) (L U : ℕ) :
    terminalWindowProbability q L U A ≤ terminalProbability q A := by
  let h : MGraph V → Pair V → ℝ≥0∞ := fun G e => if A G e then 1 else 0
  have hh (G : MGraph V) (e : Pair V) : h G e ≤ 1 := by
    dsimp [h]
    split_ifs <;> norm_num
  have hi (G : MGraph V) (e : Pair V) : 0 ≤ indicator (A G e) := by
    unfold indicator
    split_ifs <;> norm_num
  have hstep (m : ℕ) :
      terminalStepENN q m h =
        ENNReal.ofReal (terminalStep q m (fun G e => indicator (A G e))) := by
    simpa only [ofReal_indicator] using
      terminalStepENN_ofReal q m (fun G e => indicator (A G e)) hi
  have hnonneg (m : ℕ) : 0 ≤ terminalStep q m (fun G e => indicator (A G e)) := by
    apply uniformMean_nonneg
    intro x
    apply uniformMean_nonneg
    intro e
    split_ifs <;> first | exact hi _ _ | exact le_rfl
  have hwindow : ENNReal.ofReal (terminalWindowProbability q L U A) =
      ∑ m ∈ Finset.Ico L U, terminalStepENN q m h := by
    unfold terminalWindowProbability terminalWindow
    rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => hnonneg m)]
    exact Finset.sum_congr rfl (fun m _ => (hstep m).symm)
  have hfinite : terminalMeanENN q h ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (terminalMeanENN_le_one q hq hV h hh) (by simp))
  have hle : ENNReal.ofReal (terminalWindowProbability q L U A) ≤ terminalMeanENN q h := by
    rw [hwindow]
    exact ENNReal.sum_le_tsum (Finset.Ico L U)
  have hw0 : 0 ≤ terminalWindowProbability q L U A := by
    exact Finset.sum_nonneg (s := Finset.Ico L U) (fun m _ => hnonneg m)
  simpa only [ENNReal.toReal_ofReal hw0, terminalProbability, h] using
    ENNReal.toReal_mono hfinite hle

theorem S5_42AStatement_holds : ThLean.BP.S5.S5_42AStatement := by
  intro q n D hq hn y _ L U
  exact terminalWindowProbability_le q hq (by simpa using (show 2 ≤ n by omega))
    (fun G e => lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G) L U

example : ThLean.BP.S5.S5_42AStatement := S5_42AStatement_holds

end ThLean.W.S538S

module

public import ThLean.BP.S5.Main

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S5
open ThresholdFoundations

/-- Section 5 export of bridge B12, at the frozen contract's exact type. -/
theorem IdentificationColoring_of_S5 (h01 : S5_01AStatement) (h04 : S5_04Statement)
    (hcard : S5_04AStatement) (hloop : S5_04BStatement) :
    ThresholdFoundations.IdentificationColoringStatement := by
  intro V _ _ q hq B Z _ hZ
  obtain ⟨e, he⟩ := (h04 V q hq B Z hZ).1
  refine ⟨⟨e, ?_⟩, hcard V Z, hloop V q B Z, ?_⟩
  · intro τ v
    exact congrFun (he τ) v
  · exact h01 V q hq B

/-- Section 5 export of bridge B13, at the frozen contract's exact type. -/
theorem IdentificationAdvance_of_S5 (h06 : S5_06Statement) (h29 : S5_29Statement)
    (h17 : S5_17DStatement) : ThresholdFoundations.IdentificationAdvanceStatement := by
  intro V _ q hq hV
  have hpos : 0 < Fintype.card V := by omega
  have : Nonempty V := Fintype.card_pos_iff.mp hpos
  refine ⟨?_, h17 V q hq hV⟩
  intro B hB _
  refine ⟨?_, (h06 V q hq B 0 0 le_rfl).2.2.2.2, ?_⟩
  · intro D hD
    by_cases hz : D = 0
    · subst D
      rw [(h06 V q hq B 0 0 le_rfl).2.2.2.2]
      unfold identificationFailureProbability uniformProb uniformMean
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro Z _
        unfold indicator
        split <;> norm_num
      · positivity
    · exact h29 V q D hq (by omega) hD B hB
  · intro D
    exact (h06 V q hq B D (D + 1) (by omega)).2.2.1

/-- Section 5 export of thm:low-main, with its exact uniform-y quantifiers. -/
theorem LowMain_of_S5 (h40 : S5_40Statement) : ThresholdFoundations.LowMainStatement := by
  intro q hq
  obtain ⟨hC, N, hN, hbound⟩ := h40 q hq
  refine ⟨lowBoundConstant q, hC, N, by omega, ?_⟩
  intro n hn y hy
  simpa only [neg_div, Real.rpow_eq_pow] using hbound n hn y hy

/-- Section 5 export of cor:low, including every finite terminal window. -/
theorem CorLow_of_S5 (h42 : S5_42Statement) : ThresholdFoundations.CorLowStatement := by
  intro q hq
  obtain ⟨N, hN, hbound⟩ := h42 q hq
  refine ⟨N, ?_, ?_⟩
  · omega
  · intro n hn
    exact hbound n hn

example (h01 : S5_01AStatement) (h04 : S5_04Statement) (hc : S5_04AStatement)
    (hl : S5_04BStatement) : ThresholdFoundations.IdentificationColoringStatement :=
  IdentificationColoring_of_S5 h01 h04 hc hl

example (h06 : S5_06Statement) (h29 : S5_29Statement) (h17 : S5_17DStatement) :
    ThresholdFoundations.IdentificationAdvanceStatement := IdentificationAdvance_of_S5 h06 h29 h17

example (h40 : S5_40Statement) : ThresholdFoundations.LowMainStatement := LowMain_of_S5 h40
example (h42 : S5_42Statement) : ThresholdFoundations.CorLowStatement := CorLow_of_S5 h42

/-- A concrete nonempty parameter family for the strict truncation hypotheses. -/
example : ∃ N D k : ℕ, lowSizeOnset 3 ≤ N ∧ 1 ≤ D ∧ 4 * D ≤ N ∧
    Real.exp 1 * D * lowMeanBound 3 < (k : ℝ) := by
  refine ⟨max (lowSizeOnset 3) 4, 1, Nat.ceil (Real.exp 1 * lowMeanBound 3) + 1,
    le_max_left _ _, by norm_num, ?_, ?_⟩
  · simp
  · have h := Nat.le_ceil (Real.exp 1 * lowMeanBound 3)
    push_cast
    nlinarith

/-- The eventual-size contract supplies witnesses, including simultaneous log constraints. -/
example (h35 : S5_35Statement) : ∃ n : ℕ, GoodSize 3 n := by
  obtain ⟨N, hN⟩ := h35 3 (by norm_num)
  exact ⟨N, hN N le_rfl⟩

/-- The row and marginal conditions of the finite-kernel leaf can hold simultaneously. -/
example : ∃ K : Unit → Unit → ℝ,
    (∀ a b, 0 ≤ K a b) ∧ (∀ a, (∑ b, K a b) = 1) ∧
    (∀ b, uniformMean (fun a => K a b) = 1 / (Fintype.card Unit : ℝ)) := by
  exact ⟨fun _ _ => 1, by simp [uniformMean]⟩

end ThLean.BP.S5

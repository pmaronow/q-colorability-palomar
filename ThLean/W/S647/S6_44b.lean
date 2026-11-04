module

public import ThLean.BP.S6.Main

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S647

private theorem uniformMeanENN_ne_top {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ≥0∞) (hf : ∀ a, f a ≠ ∞) : uniformMeanENN f ≠ ∞ := by
  unfold ThresholdFoundations.uniformMeanENN
  apply ENNReal.div_ne_top
  · apply ENNReal.sum_ne_top.mpr
    intro a _
    exact hf a
  · have hc : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ‹Nonempty α›
    exact_mod_cast hc.ne'

private theorem uniformMeanENN_toReal {α : Type*} [Fintype α]
    (f : α → ℝ≥0∞) (hf : ∀ a, f a ≠ ∞) :
    (uniformMeanENN f).toReal = uniformMean (fun a => (f a).toReal) := by
  unfold ThresholdFoundations.uniformMeanENN ThresholdFoundations.uniformMean
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_sum (fun a _ => hf a)]
  simp

private theorem uniformMean_mono {α : Type*} [Fintype α] (f g : α → ℝ)
    (hfg : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  unfold ThresholdFoundations.uniformMean
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum (fun a _ => hfg a)
  · positivity

private theorem pair_nonempty_of_three (n : ℕ) (hn : 3 ≤ n) :
    Nonempty (Pair (Fin n)) := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨⟨s((0 : Fin n), (1 : Fin n)), ?_⟩⟩
  intro v hv
  have hv' : s((0 : Fin n), (1 : Fin n)) = s(v, v) := hv
  rw [Sym2.eq_iff] at hv'
  rcases hv' with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have h01 : (0 : Fin n) = 1 := h0.trans h1.symm
    have hval := congrArg Fin.val h01
    rw [Fin.val_zero, Fin.val_one'] at hval
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at hval
    omega
  · have h01 : (0 : Fin n) = 1 := h0.trans h1.symm
    have hval := congrArg Fin.val h01
    rw [Fin.val_zero, Fin.val_one'] at hval
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at hval
    omega

private theorem edgeTuple_nonempty {V : Type*} [Nonempty (Pair V)] (m : ℕ) :
    Nonempty (EdgeTuple V m) :=
  ⟨fun _ => Classical.choice ‹Nonempty (Pair V)›⟩

private theorem terminalStepENN_toReal {V : Type*} [Fintype V]
    [Nonempty (Pair V)] (q m : ℕ) (h : MGraph V → Pair V → ℝ≥0∞)
    (hh : ∀ G e, h G e ≠ ∞) :
    (terminalStepENN q m h).toReal =
      terminalStep q m (fun G e => (h G e).toReal) := by
  letI : Nonempty (EdgeTuple V m) := edgeTuple_nonempty m
  unfold ThresholdFoundations.terminalStepENN ThresholdFoundations.terminalStep
  have hout := uniformMeanENN_toReal
    (fun x : EdgeTuple V m =>
      uniformMeanENN (fun e : Pair V =>
        if Colorable q (tupleGraph x) ∧
            ¬ Colorable q (addPair (tupleGraph x) e)
        then h (tupleGraph x) e else 0))
    (by
      intro x
      apply uniformMeanENN_ne_top
      intro e
      split_ifs <;> simp [hh])
  rw [hout]
  congr 1
  funext x
  have hin := uniformMeanENN_toReal
    (fun e : Pair V =>
      if Colorable q (tupleGraph x) ∧
          ¬ Colorable q (addPair (tupleGraph x) e)
      then h (tupleGraph x) e else 0)
    (by
      intro e
      split_ifs <;> simp [hh])
  rw [hin]
  congr 1
  funext e
  by_cases hc : Colorable q (tupleGraph x) ∧
      ¬ Colorable q (addPair (tupleGraph x) e) <;> simp [hc]

private theorem terminalStep_event_mono {V : Type*} [Fintype V]
    (q m : ℕ) (A B : MGraph V → Pair V → Prop)
    (hAB : ∀ G e, A G e → B G e) :
    terminalStep q m (fun G e => indicator (A G e)) ≤
      terminalStep q m (fun G e => indicator (B G e)) := by
  unfold ThresholdFoundations.terminalStep
  apply uniformMean_mono
  intro x
  apply uniformMean_mono
  intro e
  by_cases hc : Colorable q (tupleGraph x) ∧
      ¬ Colorable q (addPair (tupleGraph x) e)
  · by_cases ha : A (tupleGraph x) e
    · have hb := hAB (tupleGraph x) e ha
      simp [hc, ha, hb, indicator]
    · by_cases hb : B (tupleGraph x) e
      · simp [hc, ha, hb, indicator]
      · simp [hc, ha, hb, indicator]
  · simp [hc, indicator]

private theorem terminalStepENN_ne_top {V : Type*} [Fintype V]
    [Nonempty (Pair V)] (q m : ℕ) (D : ℕ) :
    terminalStepENN q m (fun (G : MGraph V) (e : Pair V) =>
      if highEdge G D e then (1 : ℝ≥0∞) else 0) ≠ ∞ := by
  letI : Nonempty (EdgeTuple V m) := edgeTuple_nonempty m
  unfold ThresholdFoundations.terminalStepENN
  apply uniformMeanENN_ne_top
  intro x
  apply uniformMeanENN_ne_top
  intro e
  by_cases hc : Colorable q (tupleGraph x) ∧
      ¬ Colorable q (addPair (tupleGraph x) e)
  · by_cases hh : highEdge (tupleGraph x) D e <;> simp [hc, hh]
  · simp [hc]

theorem S6_44bStatement_holds : ThLean.BP.S6.S6_44bStatement := by
  intro n q M D L U hn hq hLU hUM A hA
  letI : Nonempty (Pair (Fin n)) := pair_nonempty_of_three n hn
  have hstep : ∀ m : ℕ,
      terminalStep q m (fun G e => indicator (A G e)) ≤
        (terminalStepENN (V := Fin n) q m
          (fun G e => if highEdge G D e then (1 : ℝ≥0∞) else 0)).toReal := by
    intro m
    calc
      terminalStep q m (fun G e => indicator (A G e)) ≤
          terminalStep q m (fun G e => indicator (highEdge G D e)) :=
        terminalStep_event_mono q m A (fun G e => highEdge G D e) hA
      _ = (terminalStepENN (V := Fin n) q m
          (fun G e => if highEdge G D e then (1 : ℝ≥0∞) else 0)).toReal := by
        rw [terminalStepENN_toReal (V := Fin n) q m
          (fun G e => if highEdge G D e then (1 : ℝ≥0∞) else 0)
          (by intro G e; split_ifs <;> simp)]
        congr 1
        funext G e
        by_cases hh : highEdge G D e <;> simp [hh, indicator]
  have hstepFinite : ∀ m ∈ Finset.range M,
      terminalStepENN (V := Fin n) q m
        (fun G e => if highEdge G D e then (1 : ℝ≥0∞) else 0) ≠ ∞ := by
    intro m hm
    exact terminalStepENN_ne_top (V := Fin n) q m D
  unfold ThresholdFoundations.terminalWindowProbability
    ThresholdFoundations.terminalWindow ThresholdFoundations.highTerminalProbability
  calc
    (∑ m ∈ Finset.Ico L U,
        terminalStep q m (fun G e => indicator (A G e))) ≤
      ∑ m ∈ Finset.Ico L U,
        (terminalStepENN (V := Fin n) q m
          (fun G e => if highEdge G D e then (1 : ℝ≥0∞) else 0)).toReal := by
        apply Finset.sum_le_sum
        intro m hm
        exact hstep m
    _ ≤ ∑ m ∈ Finset.range M,
        (terminalStepENN (V := Fin n) q m
          (fun G e => if highEdge G D e then (1 : ℝ≥0∞) else 0)).toReal := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢
          omega
        · intro m hm hnot
          exact ENNReal.toReal_nonneg
    _ = (∑ m ∈ Finset.range M,
        terminalStepENN (V := Fin n) q m
          (fun G e => if highEdge G D e then (1 : ℝ≥0∞) else 0)).toReal := by
        symm
        exact ENNReal.toReal_sum hstepFinite

end ThLean.W.S647

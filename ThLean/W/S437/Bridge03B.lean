import ThLean.BP.S4.Bridges

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S437

open ThresholdFoundations
open ThLean.BP.S4

private theorem tupleGraph_loopless {n k : ℕ} (x : EdgeTuple (Fin n) k) :
    Loopless (tupleGraph x) := by
  intro v
  unfold tupleGraph
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact (x i).property v hi

private theorem terminalWindowProbability_congr {n q L U : ℕ}
    {A B : MGraph (Fin n) → Pair (Fin n) → Prop}
    (hAB : ∀ G e, Loopless G → (A G e ↔ B G e)) :
    terminalWindowProbability (V := Fin n) q L U A =
      terminalProb (V := Fin n) q L U B := by
  classical
  have hInd : ∀ (k : ℕ) (x : EdgeTuple (Fin n) k) (e : Pair (Fin n)),
      indicator (A (tupleGraph x) e) = indicator (B (tupleGraph x) e) := by
    intro k x e
    apply congrArg indicator
    exact propext (hAB (tupleGraph x) e (tupleGraph_loopless x))
  simp [terminalWindowProbability, terminalWindow, terminalStep,
    terminalProb, terminalReal, hInd]

/-- Finite-window transport, conditional on the pointwise lifetime bridge. -/
theorem S4_BRIDGE_03BStatement_of_deps
    (h03a : ThLean.BP.S4.S4_BRIDGE_03AStatement) :
    ThLean.BP.S4.S4_BRIDGE_03BStatement := by
  intro q n hq hn L U D hLU y hy
  constructor
  · change terminalWindowProbability (V := Fin n) q L U
        (fun G e => lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G) = _
    apply terminalWindowProbability_congr
    intro G e hLoop
    have hLife := (h03a q n hq hn G hLoop).2.2.2.1 y hy
    constructor
    · rintro ⟨hEdge, hThreshold⟩
      exact ⟨hLife.mp hThreshold, hEdge⟩
    · rintro ⟨hThreshold, hEdge⟩
      exact ⟨hEdge, hLife.mpr hThreshold⟩
  · change terminalWindowProbability (V := Fin n) q L U
        (fun G e => bothHigh G D e ∧ ENNReal.ofReal y < lifetime q G) = _
    apply terminalWindowProbability_congr
    intro G e hLoop
    have hLife := (h03a q n hq hn G hLoop).2.2.2.1 y hy
    constructor
    · rintro ⟨hEdge, hThreshold⟩
      exact ⟨hLife.mp hThreshold, hEdge⟩
    · rintro ⟨hThreshold, hEdge⟩
      exact ⟨hEdge, hLife.mpr hThreshold⟩

end ThLean.W.S437

import ThLean.Contrib.S538.S5_42AHelpers

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S538
open ThresholdFoundations ThLean.BP.S5 ThLean.Contrib.S538

/-- Finite-window terminal mass is bounded by the all-time terminal mass. -/
theorem S5_42AStatement_of_helpers
    (hWindow : S5_42AWindowENNRepresentationStatement)
    (hFinite : S5_42AAllTimeFiniteStatement) :
    ThLean.BP.S5.S5_42AStatement := by
  intro q n D hq hn y hy L U
  unfold lowTerminalProbability terminalProbability
  have hEvent :
      (fun G : MGraph (Fin n) => fun e : Pair (Fin n) =>
        if lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G then (1 : ℝ≥0∞) else 0) =
        (fun G : MGraph (Fin n) => fun e : Pair (Fin n) =>
          @ite ℝ≥0∞ ((fun G e => lowEdge G D e ∧
            ENNReal.ofReal y < lifetime q G) G e)
            (Classical.propDecidable ((fun G e => lowEdge G D e ∧
              ENNReal.ofReal y < lifetime q G) G e)) 1 0) := by
    funext G e
    by_cases h : lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G
    · simp [h]
    · simp [h]
  have hfin := hFinite q n D hq hn y
  rw [hWindow q n D hn y L U]
  have hsum :
      (∑ m ∈ Finset.Ico L U,
        terminalStepENN (V := Fin n) q m
          (fun G e => if lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G then 1 else 0)) ≤
      terminalMeanENN (V := Fin n) q
        (fun G e => if lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G then 1 else 0) := by
    unfold terminalMeanENN
    exact ENNReal.sum_le_tsum (Finset.Ico L U)
  have hle := ENNReal.toReal_mono hfin hsum
  change _ ≤ (terminalMeanENN (V := Fin n) q
    (fun G e => @ite ℝ≥0∞ ((fun G e => lowEdge G D e ∧
      ENNReal.ofReal y < lifetime q G) G e)
      (Classical.propDecidable ((fun G e => lowEdge G D e ∧
        ENNReal.ofReal y < lifetime q G) G e)) 1 0)).toReal
  calc
    _ ≤ (terminalMeanENN (V := Fin n) q
        (fun G e => if lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G then 1 else 0)).toReal := hle
    _ = _ := congrArg ENNReal.toReal
      (congrArg (terminalMeanENN (V := Fin n) q) hEvent)

end ThLean.W.S538

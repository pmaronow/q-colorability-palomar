module

public import ThLean.BP.S6.Main
public import ThLean.BP.S6.Measure
public import ThLean.Defs.Interface

@[expose] public section

noncomputable section
open ThresholdFoundations
namespace ThLean.BP.S6

/-- Section 6 owned interface, thm:high-main, from nodes 41, 43 and the cutoff/event bridges. -/
theorem HighMain_of_S6 (h41 : S6_41Statement) (h43 : S6_43Statement)
    (ha : S6_44aStatement) (hb : S6_44bStatement) : ThresholdFoundations.HighMainStatement := by
  constructor
  · intro q hq Λ hΛ n hn hw
    exact h41 n q Λ hn hq hΛ hw
  · intro Λ hΛ
    refine ⟨sizeCutoff Λ, le_max_left _ _, ?_⟩
    intro n hn
    obtain ⟨hn3, ht⟩ := ha n Λ hΛ hn
    obtain ⟨hw, _, herr⟩ := h43 n Λ hn3 hΛ ht
    refine ⟨hw, herr, ?_⟩
    intro q hq L U hLU hU
    exact (hb n q (cap Λ n) (degreeCut n) L U hn3 hq hLU hU
      (fun G e => bothHigh G (degreeCut n) e)
      (fun G e h => bothHigh_implies_highEdge G (degreeCut n) e h)).trans
      ((h41 n q Λ hn3 hq hΛ hw).trans herr)

/-- The actual high-degree input to prop:red-split, including the extended lifetime test. -/
theorem HighLongWindow_of_S6 (h41 : S6_41Statement) (h43 : S6_43Statement)
    (ha : S6_44aStatement) (hb : S6_44bStatement)
    (Λ : ℝ) (hΛ : 0 < Λ) (n q L U : ℕ)
    (hn : sizeCutoff Λ ≤ n) (hq : 3 ≤ q) (hLU : L ≤ U) (hU : U ≤ cap Λ n) (y : ℝ) :
    highLongWindowProbability (V := Fin n) q L U (degreeCut n) y ≤ epsilon n := by
  obtain ⟨hn3, ht⟩ := ha n Λ hΛ hn
  obtain ⟨hw, _, herr⟩ := h43 n Λ hn3 hΛ ht
  exact (hb n q (cap Λ n) (degreeCut n) L U hn3 hq hLU hU
    (fun G e => bothHigh G (degreeCut n) e ∧ ENNReal.ofReal y < lifetime q G)
    (fun G e h => bothHigh_implies_highEdge G (degreeCut n) e h.1)).trans
    ((h41 n q Λ hn3 hq hΛ hw).trans herr)

end ThLean.BP.S6

module

public import ThLean.W.S434S.Normalization

@[expose] public section

noncomputable section

namespace ThLean.W.S434S
open ThresholdFoundations ThLean.BP.S4

private theorem pair_nonempty {n : ℕ} (hn : 2 ≤ n) : Nonempty (Pair (Fin n)) := by
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.mp
    (show 1 < Fintype.card (Fin n) by simpa using (show 1 < n by omega))
  refine ⟨⟨s(u, v), ?_⟩⟩
  intro w hw
  rcases Sym2.eq_iff.mp hw with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact huv (hu.trans hv.symm)
  · exact huv (hu.trans hv.symm)

/-- Finite terminal normalization and both order comparisons, with no extra premises. -/
theorem S4_BRIDGE_01CStatement_holds : ThLean.BP.S4.S4_BRIDGE_01CStatement := by
  apply ThLean.W.S434.S4_BRIDGE_01CStatement_from_normalization
  intro q n hq hn L U hLU
  haveI : Nonempty (Pair (Fin n)) := pair_nonempty (by omega)
  exact terminalProb_true_le_one q L U hLU

example : ThLean.BP.S4.S4_BRIDGE_01CStatement := S4_BRIDGE_01CStatement_holds

end ThLean.W.S434S

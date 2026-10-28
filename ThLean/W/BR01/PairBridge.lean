import ThLean.Defs.Bridge

noncomputable section

namespace ThLean.W.BR01

private theorem noLoop_iff_not_isDiag {α : Type*} [DecidableEq α]
    (z : Sym2 α) : (∀ v : α, z ≠ s(v, v)) ↔ ¬ z.IsDiag := by
  induction z using Sym2.ind with
  | h a b => simp [eq_comm]

private def pairNoDiagEquiv (n : ℕ) :
    ThresholdFoundations.Pair (Fin n) ≃ {z : Sym2 (Fin n) // ¬ z.IsDiag} where
  toFun p := ⟨p.val, (noLoop_iff_not_isDiag p.val).mp p.property⟩
  invFun p := ⟨p.val, (noLoop_iff_not_isDiag p.val).mpr p.property⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl

private theorem internalPair_card (n : ℕ) :
    Fintype.card (ThresholdFoundations.Pair (Fin n)) = n.choose 2 := by
  calc
    Fintype.card (ThresholdFoundations.Pair (Fin n)) =
        Fintype.card {z : Sym2 (Fin n) // ¬ z.IsDiag} :=
      Fintype.card_congr (pairNoDiagEquiv n)
    _ = (Fintype.card (Fin n)).choose 2 := Sym2.card_subtype_not_diag
    _ = n.choose 2 := by simp

private def challengePairEquiv (n : ℕ) :
    ThresholdChallenge.Pair n ≃ ThresholdFoundations.Pair (Fin n) where
  toFun p := ⟨p.val, by simpa [ThresholdChallenge.completeEdges] using p.property⟩
  invFun p := ⟨p.val, by simpa [ThresholdChallenge.completeEdges] using p.property⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl

private theorem completeEdges_card (n : ℕ) :
    (ThresholdChallenge.completeEdges n).card = n.choose 2 := by
  calc
    (ThresholdChallenge.completeEdges n).card =
        Fintype.card (ThresholdChallenge.Pair n) := by
      symm
      exact Fintype.card_coe _
    _ = Fintype.card (ThresholdFoundations.Pair (Fin n)) :=
      Fintype.card_congr (challengePairEquiv n)
    _ = n.choose 2 := internalPair_card n

private theorem graphsWithEdges_card (n m : ℕ) :
    (ThresholdChallenge.graphsWithEdges n m).card =
      (ThresholdChallenge.completeEdges n).card.choose m := by
  rw [ThresholdChallenge.graphsWithEdges, ← Finset.powersetCard_eq_filter]
  exact Finset.card_powersetCard m (ThresholdChallenge.completeEdges n)

theorem PairBridgeStatement_holds : ThresholdFoundations.PairBridgeStatement := by
  intro n
  have hEdges := completeEdges_card n
  have hPair := internalPair_card n
  refine ⟨hEdges, hPair, ?_, ?_⟩
  · exact ⟨challengePairEquiv n, by intro p; rfl⟩
  · intro m hm
    have hCount := graphsWithEdges_card n m
    rw [hEdges] at hCount
    exact ⟨hCount, by rw [hCount]; exact Nat.choose_pos hm⟩

example : ThresholdFoundations.PairBridgeStatement := PairBridgeStatement_holds

end ThLean.W.BR01

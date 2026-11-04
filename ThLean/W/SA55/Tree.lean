module

public import ThLean.BP.SA.Tree

@[expose] public section

noncomputable section

namespace ThLean.W.SA55

open ThresholdFoundations

theorem SA_T32aStatement_holds : ThLean.BP.SA.SA_T32aStatement := by
  intro ℓ t hℓ hbal
  induction t with
  | leaf n =>
      simp only [BlockTree.Balanced] at hbal
      rcases hbal with h | h
      · rw [h]
        simp only [BlockTree.leaves, BlockTree.size]
        constructor <;> omega
      · rw [h]
        simp only [BlockTree.leaves, BlockTree.size]
        constructor <;> omega
  | node a b iha ihb =>
      simp only [BlockTree.Balanced] at hbal
      rcases hbal with ⟨ha, hb, _, _⟩
      have hia := iha ha
      have hib := ihb hb
      constructor
      · simpa only [BlockTree.leaves, BlockTree.size, Nat.add_mul] using
          Nat.add_le_add hia.1 hib.1
      · simpa only [BlockTree.leaves, BlockTree.size, Nat.add_mul] using
          Nat.add_le_add hia.2 hib.2

end ThLean.W.SA55

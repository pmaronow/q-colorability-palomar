import ThLean.BP.SA.Tree

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA54
open ThLean.BP.SA
open ThresholdFoundations

private def treeOfList : List ℕ → BlockTree
  | [] => .leaf 0
  | [x] => .leaf x
  | x :: y :: xs =>
      let b := x :: y :: xs
      let k := (b.length + 1) / 2
      .node (treeOfList (b.take k)) (treeOfList (b.drop k))
termination_by b => b.length
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem leafList_length (t : BlockTree) : (leafList t).length = t.leaves := by
  induction t <;> simp [leafList, BlockTree.leafWeights, BlockTree.leaves, *]

private theorem balanced_of_halves (ℓ : ℕ) (t : BlockTree) (hh : Halves t)
    (hv : ∀ x ∈ leafList t, x = ℓ ∨ x = ℓ + 1) : t.Balanced ℓ := by
  induction t with
  | leaf n =>
      simp only [Halves, BlockTree.Balanced] at hh ⊢
      exact hv n (by simp [leafList, BlockTree.leafWeights])
  | node a b ihA ihB =>
      simp only [Halves, BlockTree.Balanced] at hh ⊢
      rcases hh with ⟨ha, hb, hc, hd⟩
      refine ⟨ihA ha ?_, ihB hb ?_, hc, hd⟩
      · intro x hx
        apply hv x
        change x ∈ leafList a ++ leafList b
        exact List.mem_append.mpr (Or.inl hx)
      · intro x hx
        apply hv x
        change x ∈ leafList a ++ leafList b
        exact List.mem_append.mpr (Or.inr hx)

private theorem treeOfList_spec : ∀ b : List ℕ, b ≠ [] →
    leafList (treeOfList b) = b ∧ Halves (treeOfList b) ∧
      (treeOfList b).size = b.sum
  | [], hb => False.elim (hb rfl)
  | [x], _ => by
      simp [treeOfList, leafList, BlockTree.leafWeights, Halves, BlockTree.size]
  | x :: y :: ys, _ => by
      let b := x :: y :: ys
      let k := (b.length + 1) / 2
      have hlen : 2 ≤ b.length := by simp [b]
      have hkpos : 0 < k := by omega
      have hklt : k < b.length := by omega
      have htakeLen : (b.take k).length = k := by
        simp [List.length_take, Nat.min_eq_left hklt.le]
      have hdropLen : (b.drop k).length = b.length - k := by simp
      have htake : b.take k ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [htakeLen] at this
        omega
      have hdrop : b.drop k ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [hdropLen] at this
        omega
      have hleft := treeOfList_spec (b.take k) htake
      have hright := treeOfList_spec (b.drop k) hdrop
      have htree : treeOfList b =
          BlockTree.node (treeOfList (b.take k)) (treeOfList (b.drop k)) := by
        simp [treeOfList, b, k]
      have hleftListLen : (b.take k).length = (treeOfList (b.take k)).leaves := by
        have ht := leafList_length (treeOfList (b.take k))
        rw [hleft.1] at ht
        exact ht
      have hrightListLen : (b.drop k).length = (treeOfList (b.drop k)).leaves := by
        have ht := leafList_length (treeOfList (b.drop k))
        rw [hright.1] at ht
        exact ht
      have hleftCount : (treeOfList (b.take k)).leaves = k := by
        rw [← hleftListLen, htakeLen]
      have hrightCount : (treeOfList (b.drop k)).leaves = b.length - k := by
        rw [← hrightListLen, hdropLen]
      constructor
      · rw [htree]
        change leafList (treeOfList (b.take k)) ++ leafList (treeOfList (b.drop k)) = b
        rw [hleft.1, hright.1]
        exact List.take_append_drop k b
      constructor
      · rw [htree]
        simp only [Halves]
        refine ⟨hleft.2.1, hright.2.1, ?_, ?_⟩
        · rw [hleftCount, hrightCount]
          omega
        · rw [hleftCount, hrightCount]
          omega
      · calc
          (treeOfList b).size = (treeOfList (b.take k)).size +
              (treeOfList (b.drop k)).size := by rw [htree, BlockTree.size]
          _ = (b.take k).sum + (b.drop k).sum := by rw [hleft.2.2, hright.2.2]
          _ = (b.take k ++ b.drop k).sum := by rw [List.sum_append]
          _ = b.sum := by rw [List.take_append_drop]
termination_by b _ => b.length
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem SA_T31Statement_holds : ThLean.BP.SA.SA_T31Statement := by
  intro b hb _
  have hspec := treeOfList_spec b hb
  refine ⟨treeOfList b, hspec.1, hspec.2.1, hspec.2.2, ?_⟩
  intro ℓ hall
  exact balanced_of_halves ℓ (treeOfList b) hspec.2.1 (by simpa [hspec.1] using hall)

end ThLean.W.SA54

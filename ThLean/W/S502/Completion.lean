import ThLean.BP.S5.Completion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S502

open ThLean.BP.S5 ThresholdFoundations

private theorem support_card_le {V : Type} [Fintype V] (D : ℕ)
    (x : Fin D → V) : (List.ofFn x).toFinset.card ≤ D := by
  classical
  rw [List.card_toFinset]
  exact (List.ofFn x).dedup_sublist.length_le.trans (by simp)

private theorem completion_card {V : Type} [Fintype V] (D : ℕ)
    (xs : List V) (hD : xs.toFinset.card ≤ D) :
    Fintype.card (CompletionSubset xs D) =
      (Fintype.card V - xs.toFinset.card).choose (D - xs.toFinset.card) := by
  classical
  rw [Fintype.card_subtype]
  have h := Finset.card_filter_powersetCard_subset xs.toFinset Finset.univ D
    (Finset.subset_univ _) hD
  have hset : Finset.univ.filter
      (fun Z : Finset V => xs.toFinset ⊆ Z ∧ Z.card = D) =
      (Finset.univ.powersetCard D).filter (xs.toFinset ⊆ ·) := by
    ext Z
    simp [Finset.mem_powersetCard, and_comm]
  change (Finset.univ.filter
      (fun Z : Finset V => xs.toFinset ⊆ Z ∧ Z.card = D)).card = _
  rw [hset, h]
  simp

theorem S5_28AStatement_holds : ThLean.BP.S5.S5_28AStatement := by
  intro V _ _ D hD hDV x
  classical
  dsimp
  let xs := List.ofFn x
  let w := xs.toFinset.card
  have hwD : w ≤ D := by
    exact support_card_le D x
  have hwV : w ≤ Fintype.card V :=
    (Finset.card_le_univ xs.toFinset)
  have hsub : D - w ≤ Fintype.card V - w := by omega
  have hchoose : 0 < (Fintype.card V - w).choose (D - w) :=
    Nat.choose_pos hsub
  have hcount : Fintype.card (CompletionSubset xs D) =
      (Fintype.card V - w).choose (D - w) := by
    exact completion_card D xs hwD
  refine ⟨hchoose, hcount, ?_, ?_, ?_⟩
  · have hsubtype : Fintype.card
        {Z : UniformSubset V D // xs.toFinset ⊆ Z.val} =
        (Fintype.card V - w).choose (D - w) := by
      calc
        _ = Fintype.card (CompletionSubset xs D) := by
          apply Fintype.card_congr
          refine Equiv.mk (fun Z => ⟨Z.val.val, Z.property, Z.val.property⟩) ?_ ?_ ?_
          · intro Z
            exact ⟨⟨Z.val, Z.property.2⟩, Z.property.1⟩
          · intro Z
            rfl
          · intro Z
            rfl
        _ = _ := hcount
    have hsum : (∑ Z : UniformSubset V D,
        if xs.toFinset ⊆ Z.val then 1 / ((Fintype.card V - w).choose (D - w) : ℝ) else 0) =
        (Fintype.card {Z : UniformSubset V D // xs.toFinset ⊆ Z.val} : ℝ) *
          (1 / ((Fintype.card V - w).choose (D - w) : ℝ)) := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_const]
      have hcardfilter : (Finset.univ.filter
          (fun Z : UniformSubset V D => xs.toFinset ⊆ Z.val)).card =
          Fintype.card {Z : UniformSubset V D // xs.toFinset ⊆ Z.val} := by
        rw [Fintype.card_subtype]
      rw [hcardfilter]
      simp [nsmul_eq_mul]
    calc
      (∑ Z : UniformSubset V D, completionKernel D xs Z.val) =
          ∑ Z : UniformSubset V D,
            if xs.toFinset ⊆ Z.val then
              1 / ((Fintype.card V - w).choose (D - w) : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro Z hZ
        simp [ThresholdFoundations.completionKernel, w, Z.property]
      _ = 1 := by
        rw [hsum, hsubtype]
        have hnz : ((Fintype.card V - w).choose (D - w) : ℝ) ≠ 0 := by
          exact_mod_cast hchoose.ne'
        field_simp
  · intro Z
    unfold ThLean.BP.S5.completionKernel ThresholdFoundations.completionKernel
    split_ifs with h
    · positivity
    · norm_num
  · intro Z hZ
    unfold ThLean.BP.S5.completionKernel ThresholdFoundations.completionKernel at hZ
    split_ifs at hZ with h
    · exact h.1
    · norm_num at hZ

end ThLean.W.S502

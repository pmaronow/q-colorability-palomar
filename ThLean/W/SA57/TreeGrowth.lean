import ThLean.BP.SA.Tree

noncomputable section

namespace ThLean.W.SA57

open ThresholdFoundations

theorem SA_T32cStatement_of_deps
    (hchild : ThLean.BP.SA.SA_T32bStatement) :
    ThLean.BP.SA.SA_T32cStatement := by
  intro ℓ t hℓ hbalanced
  induction t with
  | leaf n =>
      rcases hbalanced with hn | hn
      · subst n
        simp [BlockTree.height, BlockTree.size]
      · subst n
        simp [BlockTree.height, BlockTree.size]
  | node a b iha ihb =>
      rcases hbalanced with ⟨ha, hb, hleftLeaves, hrightLeaves⟩
      rcases hchild ℓ a b hℓ ⟨ha, hb, hleftLeaves, hrightLeaves⟩ with
        ⟨haLower, haUpper, hbLower, hbUpper⟩
      rcases le_total a.height b.height with hab | hba
      · have hparent :
            (ℓ : ℝ) * (4 / 3 : ℝ) ^ (b.height + 1) ≤
              ((a.size + b.size : ℕ) : ℝ) := by
          calc
            (ℓ : ℝ) * (4 / 3 : ℝ) ^ (b.height + 1) =
                ((ℓ : ℝ) * (4 / 3 : ℝ) ^ b.height) * (4 / 3 : ℝ) := by
                  rw [pow_succ]
                  ring
            _ ≤ (b.size : ℝ) * (4 / 3 : ℝ) :=
                  mul_le_mul_of_nonneg_right (ihb hb) (by norm_num)
            _ ≤ (3 * ((a.size + b.size : ℕ) : ℝ) / 4) * (4 / 3 : ℝ) :=
                  mul_le_mul_of_nonneg_right hbUpper (by norm_num)
            _ = ((a.size + b.size : ℕ) : ℝ) := by ring
        change (ℓ : ℝ) * (4 / 3 : ℝ) ^ (max a.height b.height + 1) ≤
          ((a.size + b.size : ℕ) : ℝ)
        rw [max_eq_right hab]
        exact hparent
      · have hparent :
            (ℓ : ℝ) * (4 / 3 : ℝ) ^ (a.height + 1) ≤
              ((a.size + b.size : ℕ) : ℝ) := by
          calc
            (ℓ : ℝ) * (4 / 3 : ℝ) ^ (a.height + 1) =
                ((ℓ : ℝ) * (4 / 3 : ℝ) ^ a.height) * (4 / 3 : ℝ) := by
                  rw [pow_succ]
                  ring
            _ ≤ (a.size : ℝ) * (4 / 3 : ℝ) :=
                  mul_le_mul_of_nonneg_right (iha ha) (by norm_num)
            _ ≤ (3 * ((a.size + b.size : ℕ) : ℝ) / 4) * (4 / 3 : ℝ) :=
                  mul_le_mul_of_nonneg_right haUpper (by norm_num)
            _ = ((a.size + b.size : ℕ) : ℝ) := by ring
        change (ℓ : ℝ) * (4 / 3 : ℝ) ^ (max a.height b.height + 1) ≤
          ((a.size + b.size : ℕ) : ℝ)
        rw [max_eq_left hba]
        exact hparent

end ThLean.W.SA57

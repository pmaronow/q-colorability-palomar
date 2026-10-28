import ThLean.BP.SA.Tree

namespace ThLean.W.SA56

open ThLean.BP.SA
open ThresholdFoundations

private theorem blockTree_leaves_pos : ∀ t : BlockTree, 0 < t.leaves := by
  intro t
  induction t with
  | leaf n => simp [BlockTree.leaves]
  | node a b ha hb =>
      simp only [BlockTree.leaves]
      omega

private theorem balanced_size_bounds (ℓ : ℕ) (t : BlockTree)
    (ht : t.Balanced ℓ) :
    t.leaves * ℓ ≤ t.size ∧ t.size ≤ t.leaves * (ℓ + 1) := by
  induction t with
  | leaf n =>
      simp only [BlockTree.Balanced] at ht
      rcases ht with h | h
      · subst n
        simp [BlockTree.leaves, BlockTree.size]
      · subst n
        simp [BlockTree.leaves, BlockTree.size]
  | node a b iha ihb =>
      simp only [BlockTree.Balanced] at ht
      rcases ht with ⟨ha, hb, _, _⟩
      have hba := iha ha
      have hbb := ihb hb
      constructor
      · calc
          (a.leaves + b.leaves) * ℓ = a.leaves * ℓ + b.leaves * ℓ := Nat.add_mul _ _ _
          _ ≤ a.size + b.size := Nat.add_le_add hba.1 hbb.1
      · calc
          a.size + b.size ≤ a.leaves * (ℓ + 1) + b.leaves * (ℓ + 1) :=
            Nat.add_le_add hba.2 hbb.2
          _ = (a.leaves + b.leaves) * (ℓ + 1) := by rw [Nat.add_mul]

private theorem balanced_child_size_le_three (ℓ : ℕ) (a b : BlockTree)
    (hℓ : 2 ≤ ℓ) (ha : a.Balanced ℓ) (hb : b.Balanced ℓ)
    (hleaves : a.leaves ≤ 2 * b.leaves) :
    (a.size : ℝ) ≤ 3 * (b.size : ℝ) := by
  have hsa := balanced_size_bounds ℓ a ha
  have hsb := balanced_size_bounds ℓ b hb
  have hsaR : (a.size : ℝ) ≤ (a.leaves : ℝ) * ((ℓ : ℝ) + 1) := by
    exact_mod_cast hsa.2
  have hsbR : (b.leaves : ℝ) * (ℓ : ℝ) ≤ (b.size : ℝ) := by
    exact_mod_cast hsb.1
  have hleavesR : (a.leaves : ℝ) ≤ 2 * (b.leaves : ℝ) := by
    exact_mod_cast hleaves
  have hℓR : (2 : ℝ) ≤ (ℓ : ℝ) := by
    exact_mod_cast hℓ
  have hfactor : (ℓ : ℝ) + 1 ≤ (3 / 2 : ℝ) * (ℓ : ℝ) := by
    nlinarith
  have hcoeff : 0 ≤ (3 / 2 : ℝ) * (ℓ : ℝ) := by positivity
  calc
    (a.size : ℝ) ≤ (a.leaves : ℝ) * ((ℓ : ℝ) + 1) := hsaR
    _ ≤ (a.leaves : ℝ) * ((3 / 2 : ℝ) * (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg a.leaves)
    _ ≤ (2 * (b.leaves : ℝ)) * ((3 / 2 : ℝ) * (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_right hleavesR hcoeff
    _ = 3 * ((b.leaves : ℝ) * (ℓ : ℝ)) := by ring
    _ ≤ 3 * (b.size : ℝ) := mul_le_mul_of_nonneg_left hsbR (by norm_num)

theorem SA_T32bStatement_holds : ThLean.BP.SA.SA_T32bStatement := by
  intro ℓ a b hℓ hbalanced
  have hbalanced' : a.Balanced ℓ ∧ b.Balanced ℓ ∧
      a.leaves = (a.leaves + b.leaves + 1) / 2 ∧
      b.leaves = (a.leaves + b.leaves) / 2 := by
    simpa [BlockTree.Balanced] using hbalanced
  rcases hbalanced' with ⟨ha, hb, hcounta, hcountb⟩
  have hdecomp := Nat.div_add_mod (a.leaves + b.leaves) 2
  have hquot : (a.leaves + b.leaves) / 2 = b.leaves := hcountb.symm
  rw [hquot] at hdecomp
  have hmod : (a.leaves + b.leaves) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcounts : a.leaves ≤ b.leaves + 1 ∧ b.leaves ≤ a.leaves := by omega
  have hapos := blockTree_leaves_pos a
  have hbpos := blockTree_leaves_pos b
  have hcountab : a.leaves ≤ 2 * b.leaves := by omega
  have hcountba : b.leaves ≤ 2 * a.leaves := by omega
  have hab := balanced_child_size_le_three ℓ a b hℓ ha hb hcountab
  have hba := balanced_child_size_le_three ℓ b a hℓ hb ha hcountba
  constructor
  · push_cast
    linarith
  · constructor
    · push_cast
      linarith
    · constructor
      · push_cast
        linarith
      · push_cast
        linarith

end ThLean.W.SA56

module

public import ThLean.BP.SA.Tree

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA58
open ThresholdFoundations ThLean.BP.SA

private theorem leaves_pos (t : BlockTree) : 1 ≤ t.leaves := by
  induction t with
  | leaf n => simp [BlockTree.leaves]
  | node a b ha hb => simp only [BlockTree.leaves]; omega

theorem SA_T33aStatement_of_deps
    (hsize : SA_T32aStatement) (hratio : SA_T32bStatement)
    (hgrowth : SA_T32cStatement) : SA_T33aStatement := by
  intro u₀ g hu₀ hg hanti ξ s₀ ℓ hcmp hℓ h4 t ht
  have h2 : 2 ≤ ℓ := le_trans (le_max_right s₀ 2) hℓ
  have hs₀ℓ : s₀ ≤ ℓ := le_trans (le_max_left s₀ 2) hℓ
  have h4ℓ : (4 : ℝ) ≤ (ℓ : ℝ) := by nlinarith [hu₀, h4]
  have h1ℓ : (1 : ℝ) ≤ (ℓ : ℝ) := by linarith
  have hbase : (1 : ℝ) ≤ (ℓ : ℝ) / 4 := by linarith
  let e : ℕ → ℝ := fun i => g ((ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (i + 1))
  have he_nonneg : ∀ i : ℕ, 0 ≤ e i := by
    intro i
    apply hg
    exact one_le_mul_of_one_le_of_one_le hbase (one_le_pow₀ (by norm_num))
  have hsum_mono : ∀ {m n : ℕ}, m ≤ n →
      (∑ i ∈ Finset.range m, e i) ≤ ∑ i ∈ Finset.range n, e i := by
    intro m n hmn
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
      (by intro i hi hnot; exact he_nonneg i)
  have hind : ∀ t : BlockTree, t.Balanced ℓ →
      ξ t.size ≥ ξ ℓ - g ℓ - ∑ i ∈ Finset.range t.height, e i := by
    intro t
    induction t with
    | leaf n =>
        intro hn
        rcases hn with hn | hn
        · subst n
          simp only [BlockTree.size, BlockTree.height, Finset.sum_range_zero]
          have hgn : 0 ≤ g (ℓ : ℝ) := hg (ℓ : ℝ) h1ℓ
          linarith
        · subst n
          have hstep := hcmp.2.2 ℓ hs₀ℓ
          simp only [BlockTree.size, BlockTree.height, Finset.sum_range_zero]
          linarith
    | node a b iha ihb =>
        intro hn
        rcases hn with ⟨ha, hb, hleft, hright⟩
        have htree : (BlockTree.node a b).Balanced ℓ := ⟨ha, hb, hleft, hright⟩
        have hsa : ℓ ≤ a.size := by
          have hmul := (hsize ℓ a h2 ha).1
          calc
            ℓ = ℓ * 1 := by simp
            _ ≤ ℓ * a.leaves := Nat.mul_le_mul_left ℓ (leaves_pos a)
            _ ≤ a.size := by simpa [Nat.mul_comm] using hmul
        have hsb : ℓ ≤ b.size := by
          have hmul := (hsize ℓ b h2 hb).1
          calc
            ℓ = ℓ * 1 := by simp
            _ ≤ ℓ * b.leaves := Nat.mul_le_mul_left ℓ (leaves_pos b)
            _ ≤ b.size := by simpa [Nat.mul_comm] using hmul
        have hsa₀ : s₀ ≤ a.size := le_trans hs₀ℓ hsa
        have hsb₀ : s₀ ≤ b.size := le_trans hs₀ℓ hsb
        let H := max a.height b.height
        have haH : a.height ≤ H := le_max_left _ _
        have hbH : b.height ≤ H := le_max_right _ _
        have hia : ξ a.size ≥ ξ ℓ - g ℓ - ∑ i ∈ Finset.range H, e i := by
          have hx := iha ha
          have hm := hsum_mono haH
          linarith
        have hib : ξ b.size ≥ ξ ℓ - g ℓ - ∑ i ∈ Finset.range H, e i := by
          have hx := ihb hb
          have hm := hsum_mono hbH
          linarith
        have hcmpNode := hcmp.2.1 a.size b.size hsa₀ hsb₀
        have hchildmin : ξ ℓ - g ℓ - ∑ i ∈ Finset.range H, e i ≤
            min (ξ a.size) (ξ b.size) := le_min hia hib
        have hnodeBase : (ξ ℓ - g ℓ - ∑ i ∈ Finset.range H, e i) -
            g (min a.size b.size) ≤ ξ (a.size + b.size) := by
          linarith
        have hgeo := hratio ℓ a b h2 htree
        have hminratio : ((a.size + b.size : ℕ) : ℝ) / 4 ≤
            min (a.size : ℝ) (b.size : ℝ) := le_min hgeo.1 hgeo.2.2.1
        have hgrow := hgrowth ℓ (.node a b) h2 htree
        simp only [BlockTree.height, BlockTree.size] at hgrow
        have hgrowH : (ℓ : ℝ) * (4 / 3 : ℝ) ^ (H + 1) ≤
            ((a.size + b.size : ℕ) : ℝ) := by simpa [H] using hgrow
        have harg : (ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (H + 1) ≤
            (min a.size b.size : ℝ) := by
          calc
            (ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (H + 1) =
                ((ℓ : ℝ) * (4 / 3 : ℝ) ^ (H + 1)) / 4 := by ring
            _ ≤ ((a.size + b.size : ℕ) : ℝ) / 4 :=
              div_le_div_of_nonneg_right hgrowH (by norm_num)
            _ ≤ (min a.size b.size : ℝ) := hminratio
        have hargbase : u₀ ≤ (ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (H + 1) := by
          have hp : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ (H + 1) := one_le_pow₀ (by norm_num)
          have hprod : 0 ≤ (ℓ : ℝ) / 4 * ((4 / 3 : ℝ) ^ (H + 1) - 1) :=
            mul_nonneg (by positivity) (sub_nonneg.mpr hp)
          nlinarith [h4]
        have hantiarg : g (min a.size b.size) ≤
            g ((ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (H + 1)) := by
          apply hanti
          · exact hargbase
          · exact le_trans hargbase harg
          · exact harg
        have hnodeMain : (ξ ℓ - g ℓ - ∑ i ∈ Finset.range H, e i) -
            g ((ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (H + 1)) ≤ ξ (a.size + b.size) :=
          le_trans (sub_le_sub_left hantiarg _) hnodeBase
        change ξ (a.size + b.size) ≥
          ξ ℓ - g ℓ - ∑ i ∈ Finset.range (H + 1), e i
        rw [Finset.sum_range_succ]
        dsimp [e]
        linarith
  simpa [e] using hind t ht

end ThLean.W.SA58

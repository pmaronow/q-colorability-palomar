module

public import ThLean.BP.SA.Tree

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA59
open ThLean.BP.SA
open ThresholdFoundations

theorem SA_T33bStatement_of_deps
    (h30 : SA_T30Statement)
    (h31 : SA_T31Statement)
    (h33a : SA_T33aStatement)
    (h36 : SA_T36Statement) : SA_T33bStatement := by
  intro u₀ g hg ξ s₀ hcmp
  let s₁ : ℕ := max s₀ (max 2 (Nat.ceil (4 * u₀)))
  refine ⟨s₁, ?_, ?_⟩
  · dsimp [s₁]
    omega
  · intro ℓ hs₁
    have hu₀ : 1 ≤ u₀ := hg.1
    have hg_nonneg : ∀ u : ℝ, 1 ≤ u → 0 ≤ g u := hg.2.1
    have hg_anti : AntitoneOn g (Set.Ici u₀) := hg.2.2.1
    have hs₀ : s₀ ≤ ℓ := le_trans (le_max_left _ _) hs₁
    have h2 : 2 ≤ ℓ := by
      have h₂s : 2 ≤ s₁ := by
        dsimp [s₁]
        omega
      omega
    have hceil_le : Nat.ceil (4 * u₀) ≤ ℓ := by
      have h₁ : Nat.ceil (4 * u₀) ≤ max 2 (Nat.ceil (4 * u₀)) := le_max_right _ _
      exact le_trans h₁ (le_trans (le_max_right _ _) hs₁)
    have h4 : 4 * u₀ ≤ (ℓ : ℝ) := by
      exact (Nat.le_ceil (4 * u₀)).trans (by exact_mod_cast hceil_le)
    have hmax : max s₀ 2 ≤ ℓ := max_le_iff.mpr ⟨hs₀, h2⟩
    have hpath := (h36 u₀ g hg).1 (ℓ : ℝ) h4
    have hsum_path := hpath.1
    have hpath_nonneg := hpath.2
    have hgl : 0 ≤ g (ℓ : ℝ) := hg_nonneg _ (by
      have h4lower : 4 ≤ (ℓ : ℝ) := calc
        4 = 4 * 1 := by ring
        _ ≤ 4 * u₀ := mul_le_mul_of_nonneg_left hu₀ (by norm_num)
        _ ≤ (ℓ : ℝ) := h4
      linarith)
    have herror_nonneg : 0 ≤ g (ℓ : ℝ) + pathError g (ℓ : ℝ) := add_nonneg hgl hpath_nonneg
    refine ⟨?_, ?_⟩
    · simpa using herror_nonneg
    · intro n hℓn
      rcases h30 ℓ n h2 hℓn with
        ⟨_, hquot, _, b, hb_len, hb_sum, _, _, hblocks⟩
      have hb_ne : b ≠ [] := by
        intro he
        subst b
        simp at hb_len
        omega
      have hb_pos : ∀ x ∈ b, 0 < x := by
        intro x hx
        rcases hblocks x hx with hx | hx
        · omega
        · omega
      rcases h31 b hb_ne hb_pos with ⟨t, ht_leaves, ht_halves, ht_size, ht_balanced⟩
      have hbal : t.Balanced ℓ := ht_balanced ℓ hblocks
      have hfinite := h33a u₀ g hu₀ hg_nonneg hg_anti ξ s₀ ℓ hcmp hmax h4 t hbal
      have hsum_le :
          (∑ i ∈ Finset.range t.height,
            g ((ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (i + 1))) ≤ pathError g (ℓ : ℝ) := by
        rw [pathError]
        apply hsum_path.sum_le_tsum
        intro i hi
        apply hg_nonneg
        have hbase : 1 ≤ (ℓ : ℝ) / 4 := by
          nlinarith [h4, hu₀]
        have hpow : 1 ≤ (4 / 3 : ℝ) ^ (i + 1) :=
          one_le_pow₀ (by norm_num : 1 ≤ (4 / 3 : ℝ))
        calc
          1 = 1 * 1 := by ring
          _ ≤ (ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (i + 1) :=
            mul_le_mul hbase hpow (by norm_num) (by positivity)
      have hfinite_n :
          ξ ℓ - g (ℓ : ℝ) -
            (∑ i ∈ Finset.range t.height,
              g ((ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (i + 1))) ≤ ξ n := by
        rw [ht_size, hb_sum] at hfinite
        exact hfinite
      have hfinal : ξ ℓ - (g (ℓ : ℝ) + pathError g (ℓ : ℝ)) ≤ ξ n := by
        linarith
      simpa using hfinal

end ThLean.W.SA59

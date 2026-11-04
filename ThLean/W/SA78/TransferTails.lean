module

public import ThLean.BP.SA.Transfer

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology

namespace ThLean.W.SA78

open ThLean.BP.SA
open ThresholdFoundations

private lemma binomialEvent_nonneg {B : ℕ} {p : ℝ} {A : ℕ → Prop}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binomialEvent B p A := by
  unfold binomialEvent
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg
  · unfold binomialWeight
    split_ifs with h
    · have hp₂ : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
      positivity
    · norm_num
  · unfold indicator
    split_ifs <;> norm_num

/-- X58b follows from the explicit X58a estimates by squeezing each tail by a
constant multiple of `1/n`. -/
theorem SA_X58bStatement_of_deps
    (h58a : SA_X58aStatement) : SA_X58bStatement := by
  intro d hd
  constructor
  · intro c hgap
    let gap : ℝ := c - d / 2
    let C : ℝ := d / (2 * gap ^ 2)
    have hgap_pos : 0 < gap := by dsimp [gap]; linarith
    have hden_pos : 0 < 2 * gap ^ 2 := by positivity
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hC : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
    have hvalid : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ d ≤ (n : ℝ) := by
      obtain ⟨N, hN⟩ := exists_nat_gt d
      refine Filter.eventually_atTop.2 ⟨max 2 N, ?_⟩
      intro n hn
      constructor
      · exact le_trans (le_max_left 2 N) hn
      · have hNn : (N : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (le_trans (le_max_right 2 N) hn)
        exact le_trans (le_of_lt hN) hNn
    have hnonneg : ∀ᶠ n : ℕ in atTop,
        0 ≤ binomialEvent (n.choose 2) (d / n)
          (fun k => Nat.floor (c * n) < k) := by
      filter_upwards [hvalid] with n hn
      obtain ⟨hn₂, hdn⟩ := hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hp₀ : 0 ≤ d / n := div_nonneg hd hn_pos.le
      have hp₁ : d / n ≤ 1 := (div_le_one hn_pos).2 hdn
      exact binomialEvent_nonneg hp₀ hp₁
    have hbound : ∀ᶠ n : ℕ in atTop,
        binomialEvent (n.choose 2) (d / n)
          (fun k => Nat.floor (c * n) < k) ≤ C / (n : ℝ) := by
      filter_upwards [hvalid] with n hn
      obtain ⟨hn₂, hdn⟩ := hn
      have htail := (h58a d hd).1 c n hgap hn₂ hdn
      calc
        binomialEvent (n.choose 2) (d / n)
            (fun k => Nat.floor (c * n) < k)
            ≤ d / (2 * gap ^ 2 * (n : ℝ)) := by
              simpa [gap] using htail
        _ = C / (n : ℝ) := by
              dsimp [C]
              rw [← div_div]
    exact squeeze_zero' hnonneg hbound hC
  · intro c hc hgap
    let gap : ℝ := d / 2 - c
    let C : ℝ := 2 * d / gap ^ 2
    have hgap_pos : 0 < gap := by dsimp [gap]; linarith
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hC : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
    have hvalid : ∀ᶠ n : ℕ in atTop,
        2 ≤ n ∧ d ≤ (n : ℝ) ∧ d / gap ≤ (n : ℝ) := by
      obtain ⟨N₁, hN₁⟩ := exists_nat_gt d
      obtain ⟨N₂, hN₂⟩ := exists_nat_gt (d / gap)
      refine Filter.eventually_atTop.2 ⟨max 2 (max N₁ N₂), ?_⟩
      intro n hn
      have hN₁n : (N₁ : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (le_max_left N₁ N₂) (le_trans (le_max_right 2 (max N₁ N₂)) hn))
      have hN₂n : (N₂ : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (le_max_right N₁ N₂) (le_trans (le_max_right 2 (max N₁ N₂)) hn))
      constructor
      · exact le_trans (le_max_left 2 (max N₁ N₂)) hn
      · constructor
        · exact le_trans (le_of_lt hN₁) hN₁n
        · exact le_trans (le_of_lt hN₂) hN₂n
    have hnonneg : ∀ᶠ n : ℕ in atTop,
        0 ≤ binomialEvent (n.choose 2) (d / n)
          (fun k => k < Nat.floor (c * n)) := by
      filter_upwards [hvalid] with n hn
      obtain ⟨hn₂, hdn, _⟩ := hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hp₀ : 0 ≤ d / n := div_nonneg hd hn_pos.le
      have hp₁ : d / n ≤ 1 := (div_le_one hn_pos).2 hdn
      exact binomialEvent_nonneg hp₀ hp₁
    have hbound : ∀ᶠ n : ℕ in atTop,
        binomialEvent (n.choose 2) (d / n)
          (fun k => k < Nat.floor (c * n)) ≤ C / (n : ℝ) := by
      filter_upwards [hvalid] with n hn
      obtain ⟨hn₂, hdn, hgapn⟩ := hn
      have htail := (h58a d hd).2 c n hc hgap hn₂ hdn hgapn
      calc
        binomialEvent (n.choose 2) (d / n)
            (fun k => k < Nat.floor (c * n))
            ≤ 2 * d / (gap ^ 2 * (n : ℝ)) := by
              simpa [gap] using htail
        _ = C / (n : ℝ) := by
              dsimp [C]
              rw [← div_div]
    exact squeeze_zero' hnonneg hbound hC

example (h : ThLean.BP.SA.SA_X58aStatement) :
    ThLean.BP.SA.SA_X58bStatement := SA_X58bStatement_of_deps h

end ThLean.W.SA78

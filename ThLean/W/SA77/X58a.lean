module

public import ThLean.BP.SA.Transfer

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators

namespace ThLean.W.SA77

open ThresholdFoundations
open ThLean.BP.SA

private lemma weighted_chebyshev_bound
    (B : ℕ) (w : ℕ → ℝ) (A : ℕ → Prop) (μ t v : ℝ)
    (hw : ∀ k, 0 ≤ w k)
    (hvar : (∑ k ∈ Finset.range (B + 1), w k * ((k : ℝ) - μ) ^ 2) ≤ v)
    (ht : 0 < t)
    (hA : ∀ k, A k → t ≤ |(k : ℝ) - μ|) :
    (∑ k ∈ Finset.range (B + 1), w k * indicator (A k)) ≤ v / t ^ 2 := by
  have hpoint : ∀ k ∈ Finset.range (B + 1),
      w k * indicator (A k) ≤ w k * (((k : ℝ) - μ) ^ 2 / t ^ 2) := by
    intro k hk
    by_cases hAk : A k
    · simp [indicator, hAk]
      have hsq : t ^ 2 ≤ |(k : ℝ) - μ| ^ 2 := by
        nlinarith [hA k hAk]
      have hfactor : (1 : ℝ) ≤ ((k : ℝ) - μ) ^ 2 / t ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos ht)).2
        nlinarith [sq_abs ((k : ℝ) - μ), hsq]
      simpa [indicator, hAk] using mul_le_mul_of_nonneg_left hfactor (hw k)
    · simp [indicator, hAk]
      exact mul_nonneg (hw k) (div_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    (∑ k ∈ Finset.range (B + 1), w k * indicator (A k)) ≤
        ∑ k ∈ Finset.range (B + 1), w k * (((k : ℝ) - μ) ^ 2 / t ^ 2) :=
      Finset.sum_le_sum (by intro k hk; exact hpoint k hk)
    _ = (∑ k ∈ Finset.range (B + 1), w k * ((k : ℝ) - μ) ^ 2) / t ^ 2 := by
      calc
        (∑ k ∈ Finset.range (B + 1), w k * (((k : ℝ) - μ) ^ 2 / t ^ 2)) =
            ∑ k ∈ Finset.range (B + 1), (w k * ((k : ℝ) - μ) ^ 2) / t ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [mul_div_assoc]
        _ = (∑ k ∈ Finset.range (B + 1), w k * ((k : ℝ) - μ) ^ 2) / t ^ 2 := by
          rw [← Finset.sum_div]
    _ ≤ v / t ^ 2 := by
      exact div_le_div_of_nonneg_right hvar (sq_nonneg t)

theorem SA_X58aStatement_of_deps
    (h56 : ThLean.BP.SA.SA_X56Statement) :
    ThLean.BP.SA.SA_X58aStatement := by
  intro d hd
  constructor
  · intro c n hgap hn hdn
    let B : ℕ := n.choose 2
    let p : ℝ := d / (n : ℝ)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    have hB : (B : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      dsimp [B]
      exact Nat.cast_choose_two (K := ℝ) n
    have hp0 : 0 ≤ p := by
      dsimp [p]
      exact div_nonneg hd hnR.le
    have hp1 : p ≤ 1 := by
      dsimp [p]
      exact (div_le_iff₀ hnR).2 (by simpa using hdn)
    have hBp : (B : ℝ) * p = d * ((n : ℝ) - 1) / 2 := by
      dsimp [p]
      rw [hB]
      field_simp
    rcases h56 B p hp0 hp1 with ⟨hsum, hmean, hfac, hvar, hvarle⟩
    have hw : ∀ k, 0 ≤ binomialWeight B p k := by
      intro k
      by_cases hk : k ≤ B
      · simp [binomialWeight, hk]
        positivity
      · simp [binomialWeight, hk]
    have hvarBound : (∑ k ∈ Finset.range (B + 1),
        binomialWeight B p k * ((k : ℝ) - (B : ℝ) * p) ^ 2) ≤ d * n / 2 := by
      rw [hvar]
      calc
        (B : ℝ) * p * (1 - p) ≤ (B : ℝ) * p := hvarle
        _ = d * ((n : ℝ) - 1) / 2 := hBp
        _ ≤ d * n / 2 := by nlinarith [hd]
    let t : ℝ := (c - d / 2) * n
    have ht : 0 < t := by
      dsimp [t]
      exact mul_pos (by linarith) hnR
    have hA : ∀ k, Nat.floor (c * n) < k →
        t ≤ |(k : ℝ) - (B : ℝ) * p| := by
      intro k hk
      have hcn : 0 ≤ c * (n : ℝ) := mul_nonneg (le_of_lt (lt_of_le_of_lt (by positivity) hgap)) hnR.le
      have hklt : c * (n : ℝ) < (k : ℝ) := (Nat.floor_lt hcn).mp hk
      have hdiff : t ≤ (k : ℝ) - (B : ℝ) * p := by
        dsimp [t]
        rw [hBp]
        nlinarith [hd, hklt]
      exact le_trans hdiff (le_abs_self _)
    have htail := weighted_chebyshev_bound B (binomialWeight B p) _ (B * p) t (d * n / 2)
      hw hvarBound ht hA
    change binomialEvent B p (fun k => Nat.floor (c * n) < k) ≤ _
    unfold binomialEvent
    calc
      (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * indicator (Nat.floor (c * n) < k)) ≤
          (d * n / 2) / t ^ 2 := by simpa [B, p] using htail
      _ = d / (2 * (c - d / 2) ^ 2 * n) := by
        dsimp [t]
        field_simp
  · intro c n hc hcd hn hdn hreq
    let B : ℕ := n.choose 2
    let p : ℝ := d / (n : ℝ)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    have hB : (B : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      dsimp [B]
      exact Nat.cast_choose_two (K := ℝ) n
    have hp0 : 0 ≤ p := by
      dsimp [p]
      exact div_nonneg hd hnR.le
    have hp1 : p ≤ 1 := by
      dsimp [p]
      exact (div_le_iff₀ hnR).2 (by simpa using hdn)
    have hBp : (B : ℝ) * p = d * ((n : ℝ) - 1) / 2 := by
      dsimp [p]
      rw [hB]
      field_simp
    rcases h56 B p hp0 hp1 with ⟨hsum, hmean, hfac, hvar, hvarle⟩
    have hw : ∀ k, 0 ≤ binomialWeight B p k := by
      intro k
      by_cases hk : k ≤ B
      · simp [binomialWeight, hk]
        positivity
      · simp [binomialWeight, hk]
    have hvarBound : (∑ k ∈ Finset.range (B + 1),
        binomialWeight B p k * ((k : ℝ) - (B : ℝ) * p) ^ 2) ≤ d * n / 2 := by
      rw [hvar]
      calc
        (B : ℝ) * p * (1 - p) ≤ (B : ℝ) * p := hvarle
        _ = d * ((n : ℝ) - 1) / 2 := hBp
        _ ≤ d * n / 2 := by nlinarith [hd]
    let δ : ℝ := d / 2 - c
    let t : ℝ := δ * n / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have ht : 0 < t := by dsimp [t]; positivity
    have hdnδ : d ≤ δ * n := by
      have := (div_le_iff₀ hδ).mp hreq
      dsimp [δ] at this ⊢
      nlinarith
    have hdnδ' : d ≤ (d / 2 - c) * n := by simpa [δ] using hdnδ
    have hA : ∀ k, k < Nat.floor (c * n) →
        t ≤ |(k : ℝ) - (B : ℝ) * p| := by
      intro k hk
      have hcn : 0 ≤ c * (n : ℝ) := mul_nonneg hc hnR.le
      have hklt : (k : ℝ) < c * (n : ℝ) := by
        calc
          (k : ℝ) < (Nat.floor (c * n) : ℝ) := by exact_mod_cast hk
          _ ≤ c * (n : ℝ) := Nat.floor_le hcn
      have hdiff : t ≤ (B : ℝ) * p - (k : ℝ) := by
        dsimp [t, δ]
        rw [hBp]
        nlinarith [hd, hdnδ', hklt]
      have hkn : (k : ℝ) - (B : ℝ) * p ≤ 0 := by linarith
      calc
        t ≤ (B : ℝ) * p - (k : ℝ) := hdiff
        _ = |(k : ℝ) - (B : ℝ) * p| := by
          rw [abs_of_nonpos hkn]
          ring
    have htail := weighted_chebyshev_bound B (binomialWeight B p) _ (B * p) t (d * n / 2)
      hw hvarBound ht hA
    change binomialEvent B p (fun k => k < Nat.floor (c * n)) ≤ _
    unfold binomialEvent
    calc
      (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * indicator (k < Nat.floor (c * n))) ≤
          (d * n / 2) / t ^ 2 := by simpa [B, p] using htail
      _ = 2 * d / ((d / 2 - c) ^ 2 * n) := by
        dsimp [t, δ]
        field_simp

end ThLean.W.SA77

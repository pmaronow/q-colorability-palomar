import ThLean.BP.S3.Lifetime

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology

namespace ThLean.W.S327

private theorem exp_neg_nat_eq_pow (a : ℝ) (k : ℕ) :
    Real.exp (-a * (k : ℝ)) = (Real.exp (-a)) ^ k := by
  rw [show -a * (k : ℝ) = (k : ℝ) * (-a) by ring, Real.exp_nat_mul]

private theorem exp_neg_nat_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun k : ℕ => Real.exp (-a * (k : ℝ))) := by
  have hr0 : 0 ≤ Real.exp (-a) := Real.exp_nonneg _
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hs := summable_geometric_of_lt_one hr0 hr1
  simpa only [exp_neg_nat_eq_pow] using hs

private theorem exp_neg_nat_tsum (a : ℝ) (ha : 0 < a) :
    (∑' k : ℕ, Real.exp (-a * (k : ℝ))) = 1 / (1 - Real.exp (-a)) := by
  have hr0 : 0 ≤ Real.exp (-a) := Real.exp_nonneg _
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have h := tsum_geometric_of_lt_one hr0 hr1
  simpa only [exp_neg_nat_eq_pow, one_div] using h

private theorem exp_reciprocal_bound (a : ℝ) (ha : 0 < a) :
    1 / (1 - Real.exp (-a)) ≤ 1 + 1 / a := by
  have he : 1 + a ≤ Real.exp a := by
    simpa [add_comm] using Real.add_one_le_exp a
  have hrec : Real.exp (-a) ≤ 1 / (1 + a) := by
    have hrec' : 1 / Real.exp a ≤ 1 / (1 + a) :=
      one_div_le_one_div_of_le (by positivity) he
    simpa [Real.exp_neg, one_div] using hrec'
  have hden : a / (1 + a) ≤ 1 - Real.exp (-a) := by
    have hEq : a / (1 + a) = 1 - 1 / (1 + a) := by field_simp; ring
    rw [hEq]
    linarith
  have hpos : 0 < a / (1 + a) := by positivity
  calc
    1 / (1 - Real.exp (-a)) ≤ 1 / (a / (1 + a)) :=
      one_div_le_one_div_of_le hpos hden
    _ = 1 + 1 / a := by field_simp; ring

private theorem capped_exp_tail_le (B a : ℝ) (hB : 1 ≤ B) (ha : 0 < a) :
    ∀ j : ℕ,
      min 1 (B * Real.exp (-a * ((Nat.ceil (Real.log B / a) + j : ℕ) : ℝ))) ≤
        Real.exp (-a * (j : ℝ)) := by
  let c : ℕ := Nat.ceil (Real.log B / a)
  have hBpos : 0 < B := by linarith
  have hcut : Real.log B ≤ a * (c : ℝ) := by
    have hc : Real.log B / a ≤ (c : ℝ) := by
      exact Nat.le_ceil _
    calc
      Real.log B = a * (Real.log B / a) := by field_simp [ne_of_gt ha]
      _ ≤ a * (c : ℝ) := mul_le_mul_of_nonneg_left hc ha.le
  intro j
  have hexp : B * Real.exp (-a * ((c + j : ℕ) : ℝ)) ≤ Real.exp (-a * (j : ℝ)) := by
    rw [← Real.exp_log hBpos, ← Real.exp_add]
    have hcast : ((c + j : ℕ) : ℝ) = (c : ℝ) + (j : ℝ) := by norm_cast
    apply Real.exp_le_exp.mpr
    rw [hcast]
    calc
      Real.log B + -a * ((c : ℝ) + (j : ℝ)) =
          (Real.log B - a * (c : ℝ)) + (-a * (j : ℝ)) := by ring
      _ ≤ 0 + (-a * (j : ℝ)) := add_le_add_left (sub_nonpos.mpr hcut) _
      _ = -a * (j : ℝ) := by ring
  have hmin := min_le_right 1 (B * Real.exp (-a * ((c + j : ℕ) : ℝ)))
  simpa [c, Nat.cast_add] using hmin.trans hexp

theorem S3_25Statement_holds : ThLean.BP.S3.S3_25Statement := by
  intro B a hB ha
  let c : ℕ := Nat.ceil (Real.log B / a)
  have hBpos : 0 < B := by linarith
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hcut : Real.log B ≤ a * (c : ℝ) := by
    have hc : Real.log B / a ≤ (c : ℝ) := by
      exact Nat.le_ceil _
    calc
      Real.log B = a * (Real.log B / a) := by field_simp [ne_of_gt ha]
      _ ≤ a * (c : ℝ) := mul_le_mul_of_nonneg_left hc ha.le
  have hcutUpper : (c : ℝ) ≤ Real.log B / a + 1 := by
    have hceil := Nat.ceil_lt_add_one (div_nonneg hlog ha.le)
    exact hceil.le
  have hExpSummable := exp_neg_nat_summable a ha
  have hExpTsum := exp_neg_nat_tsum a ha
  have hRecip := exp_reciprocal_bound a ha
  let f : ℕ → ℝ := fun k => min 1 (B * Real.exp (-a * (k : ℝ)))
  have htail : Summable (fun j : ℕ => f (j + c)) := by
    apply hExpSummable.of_nonneg_of_le (fun j => by positivity)
    intro j
    have h := capped_exp_tail_le B a hB ha j
    simpa [f, c, Nat.add_comm] using h
  have hsum : Summable f := by
    apply (hExpSummable.mul_left B).of_nonneg_of_le (fun k => by positivity)
    intro k
    exact min_le_right 1 (B * Real.exp (-a * (k : ℝ)))
  have hhead : (∑ k ∈ Finset.range c, f k) ≤ (c : ℝ) := by
    calc
      (∑ k ∈ Finset.range c, f k) ≤ ∑ _k ∈ Finset.range c, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact min_le_left _ _
      _ = (c : ℝ) := by simp
  have htailBound : (∑' j : ℕ, f (j + c)) ≤ ∑' j : ℕ, Real.exp (-a * (j : ℝ)) := by
    refine htail.tsum_le_tsum ?_ hExpSummable
    intro j
    have h := capped_exp_tail_le B a hB ha j
    simpa [f, c, Nat.add_comm] using h
  constructor
  · exact hsum
  constructor
  · rw [← hsum.sum_add_tsum_nat_add c]
    calc
      (∑ k ∈ Finset.range c, f k) + ∑' j : ℕ, f (j + c) ≤
          (c : ℝ) + ∑' j : ℕ, Real.exp (-a * (j : ℝ)) := add_le_add hhead htailBound
      _ = (c : ℝ) + 1 / (1 - Real.exp (-a)) := by rw [hExpTsum]
      _ ≤ (Real.log B / a + 1) + (1 + 1 / a) := add_le_add hcutUpper hRecip
      _ = Real.log B / a + 2 + 1 / a := by ring
  constructor
  · exact hExpSummable
  constructor
  · exact hExpTsum
  · exact hRecip

end ThLean.W.S327

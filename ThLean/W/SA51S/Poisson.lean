import ThLean.W.SA51S.Means

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA51S
open ThresholdFoundations

lemma poisson_hasSum (z : ℝ) : HasSum (poissonWeight z) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp z).mul_left (Real.exp (-z))
  change HasSum (fun m => Real.exp (-z) * z ^ m / (Nat.factorial m : ℝ)) 1
  simpa only [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    mul_div_assoc] using h

lemma poisson_nonneg {z : ℝ} (hz : 0 ≤ z) (m : ℕ) : 0 ≤ poissonWeight z m := by
  unfold poissonWeight
  positivity

lemma poisson_summable_bounded {z : ℝ} (hz : 0 ≤ z) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m ∧ a m ≤ 1) : Summable (fun m => poissonWeight z m * a m) := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (poisson_nonneg hz m) (ha m).1)
    (fun m => ?_) (poisson_hasSum z).summable
  simpa using mul_le_mul_of_nonneg_left (ha m).2 (poisson_nonneg hz m)

lemma poisson_binomial (c s t : ℝ) (hs : 0 < s) (ht : 0 < t) (i j : ℕ) :
    poissonWeight (c * (s+t)) (i+j) * ((i+j).choose i : ℝ) *
        (s / (s+t)) ^ i * (t / (s+t)) ^ j =
      poissonWeight (c*s) i * poissonWeight (c*t) j := by
  have hst : s + t ≠ 0 := ne_of_gt (add_pos hs ht)
  have hi : (Nat.factorial i : ℝ) ≠ 0 := by positivity
  have hj : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hij : (Nat.factorial (i+j) : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_choose ℝ (by omega)]
  simp only [Nat.add_sub_cancel_left]
  unfold poissonWeight
  rw [show -(c * (s+t)) = -(c*s) + -(c*t) by ring, Real.exp_add]
  simp only [mul_pow, pow_add, div_pow]
  field_simp
  <;> ring

lemma poisson_binomial_sum (c s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (a b : ℕ → ℝ) (m : ℕ) :
    poissonWeight (c*(s+t)) m * (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
      (m.choose ij.1 : ℝ) * (s/(s+t)) ^ ij.1 * (t/(s+t)) ^ ij.2 *
        (a ij.1 * b ij.2)) =
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
      (poissonWeight (c*s) ij.1 * a ij.1) * (poissonWeight (c*t) ij.2 * b ij.2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hm : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← hm]
  calc
    _ = (poissonWeight (c*(s+t)) (ij.1+ij.2) * ((ij.1+ij.2).choose ij.1 : ℝ) *
        (s/(s+t)) ^ ij.1 * (t/(s+t)) ^ ij.2) * (a ij.1 * b ij.2) := by ring
    _ = _ := by rw [poisson_binomial c s t hs ht]; ring

lemma poisson_convolution_summable (c s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (a b : ℕ → ℝ)
    (hA : Summable (fun i => poissonWeight (c*s) i * a i))
    (hB : Summable (fun j => poissonWeight (c*t) j * b j)) :
    Summable (fun m => poissonWeight (c*(s+t)) m *
      (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
        (m.choose ij.1 : ℝ) * (s/(s+t)) ^ ij.1 * (t/(s+t)) ^ ij.2 *
          (a ij.1 * b ij.2))) := by
  have h := summable_sum_mul_antidiagonal_of_summable_norm' hA.norm hA hB.norm hB
  exact h.congr (fun m => (poisson_binomial_sum c s t hs ht a b m).symm)

/-- Poissonization of the binomial convolution gives the product of the two laws. -/
lemma poisson_convolution (c s t : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (ht : 0 < t)
    (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    poissonMixture (c * (s+t)) (fun m => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
      (m.choose ij.1 : ℝ) * (s/(s+t)) ^ ij.1 * (t/(s+t)) ^ ij.2 *
        (a ij.1 * b ij.2)) = poissonMixture (c*s) a * poissonMixture (c*t) b := by
  have hA := poisson_summable_bounded (mul_nonneg hc hs.le) a ha
  have hB := poisson_summable_bounded (mul_nonneg hc ht.le) b hb
  unfold poissonMixture
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA.norm hB.norm]
  apply tsum_congr
  intro m
  exact poisson_binomial_sum c s t hs ht a b m

end ThLean.W.SA51S

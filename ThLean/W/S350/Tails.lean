import ThLean.BP.S3.Tails

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S350
open ThresholdFoundations ThLean.BP.S3

private theorem binomialWeight_sum (n : ℕ) (p : ℝ) :
    (∑ j ∈ Finset.range (n + 1), binomialWeight n p j) = 1 := by
  calc
    (∑ j ∈ Finset.range (n + 1), binomialWeight n p j) =
        ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [binomialWeight, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)]
    _ = ∑ j ∈ Finset.range (n + 1),
          p ^ j * (1 - p) ^ (n - j) * (n.choose j : ℝ) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
    _ = 1 := by ring

private theorem binomialWeight_shift_le (m k j : ℕ) (p : ℝ)
    (hkj : k ≤ j) (hjm : j ≤ m) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialWeight m p j ≤
      ((m.choose k : ℝ) * p ^ k) * binomialWeight (m-k) p (j-k) := by
  have hcoeff : (m.choose j : ℝ) ≤
      (m.choose k : ℝ) * ((m-k).choose (j-k) : ℝ) := by
    have hmul := Nat.choose_mul (n := m) (k := j) (s := k) hkj
    have hone : 1 ≤ j.choose k := Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos hkj).ne'
    have hle := Nat.mul_le_mul_left (m.choose j) hone
    have hmul' : m.choose j * j.choose k = m.choose k * (m-k).choose (j-k) := hmul
    exact_mod_cast (by simpa [hmul'] using hle)
  have hp0 : 0 ≤ 1-p := by linarith
  have hpow : p^j = p^k * p^(j-k) := by
    have hj_eq : k + (j-k) = j := Nat.add_sub_of_le hkj
    calc
      p^j = p^(k + (j-k)) := congrArg (fun n : ℕ => p^n) hj_eq.symm
      _ = p^k * p^(j-k) := pow_add p k (j-k)
  have heq : m - j = (m-k) - (j-k) := by omega
  change (if j ≤ m then (m.choose j : ℝ) * p ^ j * (1-p) ^ (m-j) else 0) ≤
    ((m.choose k : ℝ) * p ^ k) *
      (if j-k ≤ m-k then ((m-k).choose (j-k) : ℝ) * p^(j-k) *
        (1-p)^((m-k)-(j-k)) else 0)
  simp only [if_pos hjm, if_pos (Nat.sub_le_sub_right hjm k)]
  calc
    (m.choose j : ℝ) * p^j * (1-p) ^ (m-j) =
        ((m.choose j : ℝ) * (p ^ k * p ^ (j-k))) * (1-p) ^ ((m-k)-(j-k)) := by
          rw [hpow, heq]
    _ = ((m.choose j : ℝ) * p ^ k) * (p ^ (j-k) * (1-p) ^ ((m-k)-(j-k))) := by
          ring
    _ ≤ (((m.choose k : ℝ) * ((m-k).choose (j-k) : ℝ)) * p ^ k) *
        (p ^ (j-k) * (1-p) ^ ((m-k)-(j-k))) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hp k)
          · exact mul_nonneg (pow_nonneg hp (j-k))
              (pow_nonneg hp0 ((m-k)-(j-k)))
    _ = ((m.choose k : ℝ) * p ^ k) *
        ((m-k).choose (j-k) * p ^ (j-k) * (1-p) ^ ((m-k)-(j-k))) := by ring

private theorem binomialTail_le_choose_mul_pow (m k : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialTail m p k ≤ (m.choose k : ℝ) * p^k := by
  by_cases hkm : k ≤ m
  · have htail : binomialTail m p k =
        ∑ j ∈ Finset.Icc k m, binomialWeight m p j := by
      unfold binomialTail
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨hjm, hkj⟩
        exact ⟨by exact_mod_cast hkj, Nat.lt_succ_iff.mp hjm⟩
      · rintro ⟨hkj, hjm⟩
        exact ⟨by omega, by exact_mod_cast hkj⟩
    rw [htail]
    calc
      (∑ j ∈ Finset.Icc k m, binomialWeight m p j) ≤
          ∑ j ∈ Finset.Icc k m,
            ((m.choose k : ℝ) * p^k) * binomialWeight (m-k) p (j-k) := by
              apply Finset.sum_le_sum
              intro j hj
              exact binomialWeight_shift_le m k j p (Finset.mem_Icc.mp hj).1
                (Finset.mem_Icc.mp hj).2 hp hp1
      _ = ((m.choose k : ℝ) * p^k) *
          (∑ j ∈ Finset.Icc k m, binomialWeight (m-k) p (j-k)) := by
            rw [Finset.mul_sum]
      _ = ((m.choose k : ℝ) * p^k) *
          (∑ j ∈ Finset.range (m-k+1), binomialWeight (m-k) p j) := by
            congr 1
            apply Finset.sum_bij (fun j _ => j-k)
            · intro j hj
              simp only [Finset.mem_Icc] at hj
              simp only [Finset.mem_range]
              omega
            · intro a ha b hb hab
              simp only [Finset.mem_Icc] at ha hb
              omega
            · intro b hb
              simp only [Finset.mem_range] at hb
              refine ⟨k+b, ?_, ?_⟩
              · simp only [Finset.mem_Icc]
                omega
              · omega
            · intro j hj
              simp [binomialWeight, (Finset.mem_Icc.mp hj).1,
                Nat.sub_sub_sub_cancel_right]
      _ = (m.choose k : ℝ) * p^k := by simp [binomialWeight_sum]
  · have hzero : binomialTail m p k = 0 := by
      unfold binomialTail
      apply Finset.sum_eq_zero
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hnot : ¬ ((k : ℝ) ≤ (j : ℝ)) := by
        exact_mod_cast (not_le_of_gt (lt_of_le_of_lt hjm (Nat.lt_of_not_ge hkm)))
      simp [hnot]
    rw [hzero, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkm)]
    simp

theorem S3_43Statement_of_deps (h42 : S3_42Statement) : S3_43Statement := by
  intro m k p hk hp hp1
  refine ⟨binomialTail_le_choose_mul_pow m k p hp hp1, ?_⟩
  have hp0 : 0 ≤ p^k := pow_nonneg hp k
  have hchoose := (h42.2.1 m k hk).1
  have hpow := (h42.2.1 m k hk).2
  calc
    (m.choose k : ℝ) * p^k ≤ ((m : ℝ)^k / (k.factorial : ℝ)) * p^k :=
      mul_le_mul_of_nonneg_right hchoose hp0
    _ ≤ (Real.exp 1 * (m : ℝ) / k)^k * p^k :=
      mul_le_mul_of_nonneg_right hpow hp0
    _ = (Real.exp 1 * (m : ℝ) * p / k)^k := by
      rw [← mul_pow]
      congr 1
      field_simp

end ThLean.W.S350

import ThLean.BP.SA.Transfer

noncomputable section
open scoped BigOperators

namespace ThLean.W.SA75
open ThLean.BP.SA
open ThresholdFoundations

private lemma binomialWeight_sum (B : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (B + 1), binomialWeight B p k) = 1 := by
  calc
    (∑ k ∈ Finset.range (B + 1), binomialWeight B p k) =
        ∑ k ∈ Finset.range (B + 1),
          (p ^ k * (1 - p) ^ (B - k)) * (B.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkB : k ≤ B := by
        have := Finset.mem_range.mp hk
        omega
      rw [binomialWeight, if_pos hkB]
      ring
    _ = (p + (1 - p)) ^ B := by
      rw [add_pow]
    _ = 1 := by ring

private lemma binomialWeight_first_moment (B : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ)) =
      (B : ℝ) * p := by
  cases B with
  | zero => simp [binomialWeight]
  | succ t =>
    rw [Finset.sum_range_succ' (fun k => binomialWeight (t + 1) p k * (k : ℝ)) (t + 1)]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    calc
      (∑ k ∈ Finset.range (t + 1),
          binomialWeight (t + 1) p (k + 1) * ((k + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.range (t + 1),
          (((t + 1 : ℕ) : ℝ) * p) * binomialWeight t p k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkB : k ≤ t := by
          have := Finset.mem_range.mp hk
          omega
        have hchooseNat := Nat.add_one_mul_choose_eq t k
        have hchoose : ((t + 1 : ℕ) : ℝ) * (t.choose k : ℝ) =
            ((t + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast hchooseNat
        have hsub : t + 1 - (k + 1) = t - k := by omega
        rw [binomialWeight, if_pos (show k + 1 ≤ t + 1 by omega),
          binomialWeight, if_pos hkB, hsub, pow_succ]
        linear_combination -hchoose * (p ^ k * p * (1 - p) ^ (t - k))
      _ = (((t + 1 : ℕ) : ℝ) * p) *
          (∑ k ∈ Finset.range (t + 1), binomialWeight t p k) := by
        rw [Finset.mul_sum]
      _ = (((t + 1 : ℕ) : ℝ) * p) * 1 := by rw [binomialWeight_sum]
      _ = (((t + 1 : ℕ) : ℝ) * p) := by rw [mul_one]

private lemma binomialWeight_second_factorial_moment (B : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (B + 1),
      binomialWeight B p k * (k : ℝ) * ((k : ℝ) - 1)) =
      (B : ℝ) * ((B : ℝ) - 1) * p ^ 2 := by
  cases B with
  | zero => simp [binomialWeight]
  | succ b =>
    cases b with
    | zero => norm_num [Finset.sum_range_succ, Finset.sum_range_succ', binomialWeight]
    | succ t =>
      let g : ℕ → ℝ := fun k =>
        binomialWeight (t + 2) p k * (k : ℝ) * ((k : ℝ) - 1)
      change (∑ k ∈ Finset.range (t + 2 + 1), g k) = _
      rw [Finset.sum_range_succ' g (t + 2)]
      rw [Finset.sum_range_succ' (fun k => g (k + 1)) (t + 1)]
      have hg0 : g 0 = 0 := by simp [g]
      have hg1 : g 1 = 0 := by simp [g]
      rw [hg0, hg1, add_zero, add_zero]
      calc
        (∑ k ∈ Finset.range (t + 1), g (k + 2)) =
            ∑ k ∈ Finset.range (t + 1),
              ((((t + 2 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) * p ^ 2) *
                binomialWeight t p k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkB : k ≤ t := by
            have := Finset.mem_range.mp hk
            omega
          have hchooseNat : (t + 2) * (t + 1) * t.choose k =
              (t + 2).choose (k + 2) * (k + 2) * (k + 1) := by
            calc
              (t + 2) * (t + 1) * t.choose k =
                  (t + 2) * ((t + 1) * t.choose k) := by ring
              _ = (t + 2) * ((t + 1).choose (k + 1) * (k + 1)) := by
                rw [Nat.add_one_mul_choose_eq t k]
              _ = ((t + 2) * (t + 1).choose (k + 1)) * (k + 1) := by ring
              _ = ((t + 2).choose (k + 2) * (k + 2)) * (k + 1) := by
                rw [Nat.add_one_mul_choose_eq (t + 1) (k + 1)]
              _ = (t + 2).choose (k + 2) * (k + 2) * (k + 1) := by ring
          have hchoose : ((t + 2 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) *
              (t.choose k : ℝ) = ((t + 2).choose (k + 2) : ℝ) *
                ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
            exact_mod_cast hchooseNat
          have hsub : t + 2 - (k + 2) = t - k := by omega
          have hpred : ((k + 2 : ℕ) : ℝ) - 1 = ((k + 1 : ℕ) : ℝ) := by
            push_cast
            ring
          dsimp only [g]
          rw [binomialWeight, if_pos (show k + 2 ≤ t + 2 by omega), hsub,
            pow_add, hpred, binomialWeight, if_pos hkB]
          calc
            ((t + 2).choose (k + 2) : ℝ) * (p ^ k * p ^ 2) *
                (1 - p) ^ (t - k) * ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) =
              (((t + 2).choose (k + 2) : ℝ) * ((k + 2 : ℕ) : ℝ) *
                ((k + 1 : ℕ) : ℝ)) * (p ^ k * p ^ 2 * (1 - p) ^ (t - k)) := by ring
            _ = ((((t + 2 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) *
                (t.choose k : ℝ)) * (p ^ k * p ^ 2 * (1 - p) ^ (t - k))) := by
              rw [← hchoose]
            _ = (((t + 2 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) * p ^ 2) *
                ((t.choose k : ℝ) * p ^ k * (1 - p) ^ (t - k)) := by ring
        _ = ((((t + 2 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) * p ^ 2)) *
            (∑ k ∈ Finset.range (t + 1), binomialWeight t p k) := by
          rw [Finset.mul_sum]
        _ = ((((t + 2 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) * p ^ 2)) * 1 := by
          rw [binomialWeight_sum]
        _ = (((t + 2 : ℕ) : ℝ) * (((t + 2 : ℕ) : ℝ) - 1) * p ^ 2) := by
          push_cast
          ring

private lemma binomialWeight_moment_summable (B r : ℕ) (p : ℝ) :
    Summable (fun k : ℕ => binomialWeight B p k * (k : ℝ) ^ r) := by
  apply summable_of_ne_finset_zero (s := Finset.range (B + 1))
  intro k hk
  have hkB : B < k := by
    have hnot : ¬ k < B + 1 := by simpa using hk
    omega
  simp [ThresholdFoundations.binomialWeight, Nat.not_le_of_gt hkB]

private lemma binomialWeight_variance (B : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (B + 1),
      binomialWeight B p k * ((k : ℝ) - (B : ℝ) * p) ^ 2) =
      (B : ℝ) * p * (1 - p) := by
  let μ : ℝ := (B : ℝ) * p
  have hmass := binomialWeight_sum B p
  have hfirst := binomialWeight_first_moment B p
  have hsecond := binomialWeight_second_factorial_moment B p
  have hsq : (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ) ^ 2) =
      (∑ k ∈ Finset.range (B + 1),
        binomialWeight B p k * (k : ℝ) * ((k : ℝ) - 1)) +
        (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ)) := by
    calc
      (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ) ^ 2) =
          ∑ k ∈ Finset.range (B + 1),
            binomialWeight B p k * ((k : ℝ) * ((k : ℝ) - 1) + (k : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (∑ k ∈ Finset.range (B + 1),
            binomialWeight B p k * (k : ℝ) * ((k : ℝ) - 1)) +
          (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hvar : (∑ k ∈ Finset.range (B + 1),
      binomialWeight B p k * ((k : ℝ) - μ) ^ 2) =
      (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ) ^ 2) -
        2 * μ * (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ)) +
        μ ^ 2 * (∑ k ∈ Finset.range (B + 1), binomialWeight B p k) := by
    calc
      (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * ((k : ℝ) - μ) ^ 2) =
          ∑ k ∈ Finset.range (B + 1),
            (binomialWeight B p k * (k : ℝ) ^ 2 -
              2 * μ * (binomialWeight B p k * (k : ℝ)) +
              μ ^ 2 * binomialWeight B p k) := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [μ]
        ring
      _ = (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ) ^ 2) -
          (∑ k ∈ Finset.range (B + 1), 2 * μ * (binomialWeight B p k * (k : ℝ))) +
          (∑ k ∈ Finset.range (B + 1), μ ^ 2 * binomialWeight B p k) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ) ^ 2) -
          2 * μ * (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ)) +
          μ ^ 2 * (∑ k ∈ Finset.range (B + 1), binomialWeight B p k) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  calc
    (∑ k ∈ Finset.range (B + 1),
        binomialWeight B p k * ((k : ℝ) - (B : ℝ) * p) ^ 2) =
      (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ) ^ 2) -
        2 * μ * (∑ k ∈ Finset.range (B + 1), binomialWeight B p k * (k : ℝ)) +
        μ ^ 2 * (∑ k ∈ Finset.range (B + 1), binomialWeight B p k) := by
      simpa [μ] using hvar
    _ = (B : ℝ) * p * (1 - p) := by
      rw [hsq, hsecond, hfirst, hmass]
      dsimp [μ]
      ring

theorem SA_X56Statement_holds : ThLean.BP.SA.SA_X56Statement := by
  intro B p hp hp1
  refine ⟨?_, binomialWeight_first_moment B p,
    binomialWeight_second_factorial_moment B p, binomialWeight_variance B p, ?_⟩
  · intro r
    exact binomialWeight_moment_summable B r p
  · have hB : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
    nlinarith [mul_nonneg hB (sq_nonneg p)]

example : ThLean.BP.SA.SA_X56Statement := SA_X56Statement_holds

end ThLean.W.SA75

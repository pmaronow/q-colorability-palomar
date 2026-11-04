module

public import ThLean.BP.S6.Analytic

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S651

private def boolSetEquiv (m : ℕ) : (Fin m → Bool) ≃ Finset (Fin m) where
  toFun x := Finset.univ.filter (fun i => x i = true)
  invFun s := fun i => decide (i ∈ s)
  left_inv x := by
    funext i
    by_cases h : x i = true <;> simp [h]
  right_inv s := by
    ext i
    simp

private theorem successCount_eq_card (m : ℕ) (x : Fin m → Bool) :
    ThLean.BP.S6.successCount x = (boolSetEquiv m x).card := by
  rfl

private theorem boolBernoulli_tail (m k : ℕ) (p : ℝ) :
    (∑ x : Fin m → Bool,
      ThLean.BP.S6.bernoulliWeight p x *
        indicator (k ≤ ThLean.BP.S6.successCount x)) =
      ThresholdFoundations.binomialTail m p (k : ℝ) := by
  classical
  let f : Finset (Fin m) → ℝ := fun s =>
    (p ^ s.card * (1 - p) ^ (m - s.card)) * indicator (k ≤ s.card)
  calc
    _ = ∑ x : Fin m → Bool, f (boolSetEquiv m x) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [f, ThLean.BP.S6.bernoulliWeight, successCount_eq_card]
    _ = ∑ s : Finset (Fin m), f s := Equiv.sum_comp (boolSetEquiv m) f
    _ = ∑ r ∈ Finset.range (m + 1),
          ∑ s ∈ (Finset.univ.filter (fun s : Finset (Fin m) => s.card = r)), f s := by
      have hfilter :
          (Finset.univ.filter (fun s : Finset (Fin m) =>
            s.card ∈ Finset.range (m + 1))) = Finset.univ := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
        simp only [Nat.lt_succ_iff]
        constructor
        · intro _
          trivial
        · intro _
          calc
            s.card ≤ (Finset.univ : Finset (Fin m)).card :=
              Finset.card_le_card (Finset.subset_univ s)
            _ = m := by simp
      calc
        _ = ∑ s ∈ (Finset.univ.filter (fun s : Finset (Fin m) =>
              s.card ∈ Finset.range (m + 1))), f s := by rw [hfilter]
        _ = _ := (Finset.sum_fiberwise_eq_sum_filter
          (Finset.univ : Finset (Finset (Fin m))) (Finset.range (m + 1))
          (fun s : Finset (Fin m) => s.card) f).symm
    _ = ∑ r ∈ Finset.range (m + 1),
          (if k ≤ r then ((m.choose r : ℝ) * p ^ r * (1 - p) ^ (m - r)) else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrm : r ≤ m := by
        have := Finset.mem_range.mp hr
        omega
      have hsets :
          Finset.univ.filter (fun s : Finset (Fin m) => s.card = r) =
            Finset.powersetCard r Finset.univ := by
        ext s
        simp [Finset.mem_powersetCard]
      rw [hsets]
      calc
        _ = ∑ s ∈ Finset.powersetCard r (Finset.univ : Finset (Fin m)),
              (p ^ r * (1 - p) ^ (m - r)) * indicator (k ≤ r) := by
          apply Finset.sum_congr rfl
          intro s hs
          simp [f, (Finset.mem_powersetCard.mp hs).2]
        _ = ((Finset.powersetCard r (Finset.univ : Finset (Fin m))).card : ℝ) *
              ((p ^ r * (1 - p) ^ (m - r)) * indicator (k ≤ r)) := by
          simp
        _ = if k ≤ r then ((m.choose r : ℝ) * p ^ r * (1 - p) ^ (m - r)) else 0 := by
          rw [Finset.card_powersetCard]
          simp [indicator]
          split_ifs <;> simp [mul_assoc, mul_left_comm, mul_comm]
    _ = ThresholdFoundations.binomialTail m p (k : ℝ) := by
      simp [ThresholdFoundations.binomialTail, ThresholdFoundations.binomialWeight]
      apply Finset.sum_congr rfl
      intro r hr
      have hrm : r ≤ m := by
        have := Finset.mem_range.mp hr
        omega
      simp [hrm]

private theorem binomialTail_le_choose_pow (m k : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ThresholdFoundations.binomialTail m p (k : ℝ) ≤ (m.choose k : ℝ) * p ^ k := by
  classical
  by_cases hkm : k ≤ m
  · let A : ℕ → ℝ := fun r =>
      (m.choose r : ℝ) * p ^ r * (1 - p) ^ (m - r)
    let B : ℕ → ℝ := fun r =>
      ((m - k).choose (r - k) : ℝ) * p ^ (r - k) * (1 - p) ^ ((m - k) - (r - k))
    have htail : ThresholdFoundations.binomialTail m p (k : ℝ) =
        ∑ r ∈ Finset.range (m + 1), if k ≤ r then A r else 0 := by
      simp [ThresholdFoundations.binomialTail, ThresholdFoundations.binomialWeight,
        A]
      apply Finset.sum_congr rfl
      intro r hr
      have hrm : r ≤ m := by
        have hr' : r < m + 1 := Finset.mem_range.mp hr
        omega
      simp [hrm]
    have hterm : ∀ r ∈ Finset.range (m + 1),
        (if k ≤ r then A r else 0) ≤
          if k ≤ r then ((m.choose k : ℝ) * p ^ k) * B r else 0 := by
      intro r hr
      by_cases hkr : k ≤ r
      · have hrm : r ≤ m := by
          have hr' : r < m + 1 := Finset.mem_range.mp hr
          omega
        have hcoeff : (m.choose r : ℝ) * (r.choose k : ℝ) =
            (m.choose k : ℝ) * ((m - k).choose (r - k) : ℝ) := by
          exact_mod_cast (Nat.choose_mul hkr)
        have hchoose : 1 ≤ (r.choose k : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos hkr))
        have hexp : m - r = (m - k) - (r - k) := by omega
        have hpow : p ^ r = p ^ k * p ^ (r - k) := by
          calc
            p ^ r = p ^ (k + (r - k)) := by congr 1; omega
            _ = p ^ k * p ^ (r - k) := by rw [pow_add]
        have heq : A r * (r.choose k : ℝ) = ((m.choose k : ℝ) * p ^ k) * B r := by
          calc
            A r * (r.choose k : ℝ) =
                ((m.choose r : ℝ) * (r.choose k : ℝ)) * p ^ r * (1 - p) ^ (m - r) := by
                  simp [A]
                  ring
            _ = ((m.choose k : ℝ) * ((m - k).choose (r - k) : ℝ)) *
                  p ^ r * (1 - p) ^ (m - r) := by rw [hcoeff]
            _ = ((m.choose k : ℝ) * p ^ k) * B r := by
                  rw [hpow, hexp]
                  simp only [B]
                  ring
        have hA : 0 ≤ A r := by
          dsimp [A]
          positivity
        have : 0 ≤ A r * ((r.choose k : ℝ) - 1) :=
          mul_nonneg hA (sub_nonneg.mpr hchoose)
        have hAC : A r ≤ A r * (r.choose k : ℝ) := by nlinarith
        simpa [hkr] using hAC.trans (le_of_eq heq)
      · simp [hkr]
    calc
      ThresholdFoundations.binomialTail m p (k : ℝ) =
          ∑ r ∈ Finset.range (m + 1), if k ≤ r then A r else 0 := htail
      _ ≤ ∑ r ∈ Finset.range (m + 1),
            if k ≤ r then ((m.choose k : ℝ) * p ^ k) * B r else 0 :=
          Finset.sum_le_sum hterm
      _ = ((m.choose k : ℝ) * p ^ k) *
            ∑ r ∈ Finset.range (m + 1), if k ≤ r then B r else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          by_cases hkr : k ≤ r <;> simp [hkr, mul_assoc]
      _ = ((m.choose k : ℝ) * p ^ k) *
            ∑ j ∈ Finset.range ((m + 1) - k), B (k + j) := by
          have hset : (Finset.range (m + 1)).filter (fun r => k ≤ r) =
              Finset.Ico k (m + 1) := by
            ext r
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
            omega
          congr 1
          rw [← Finset.sum_filter, hset, Finset.sum_Ico_eq_sum_range]
      _ = ((m.choose k : ℝ) * p ^ k) * 1 := by
          congr 1
          calc
            (∑ j ∈ Finset.range ((m + 1) - k), B (k + j)) =
                ∑ j ∈ Finset.range (m - k + 1),
                  ((m - k).choose j : ℝ) * p ^ j * (1 - p) ^ ((m - k) - j) := by
                have hrange : (m + 1) - k = (m - k) + 1 := by omega
                rw [hrange]
                apply Finset.sum_congr rfl
                intro j hj
                simp [B]
            _ = 1 := by
                calc
                  _ = ∑ j ∈ Finset.range ((m - k) + 1),
                        p ^ j * (1 - p) ^ ((m - k) - j) * ((m - k).choose j : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
                  _ = (p + (1 - p)) ^ (m - k) := by rw [add_pow]
                  _ = 1 := by ring
      _ = (m.choose k : ℝ) * p ^ k := by ring
  · have hkm' : m < k := by omega
    have hzero : ThresholdFoundations.binomialTail m p (k : ℝ) = 0 := by
      unfold ThresholdFoundations.binomialTail
      apply Finset.sum_eq_zero
      intro r hr
      have hr' : r < m + 1 := Finset.mem_range.mp hr
      have hrm : r ≤ m := by omega
      have hkr : ¬ k ≤ r := by omega
      simp [hkr]
    rw [hzero]
    simp [Nat.choose_eq_zero_of_lt hkm']

theorem S6_X04Statement_of_deps
    (h03 : ThLean.BP.S6.S6_X03Statement) :
    ThLean.BP.S6.S6_X04Statement := by
  intro m k p hk hp hp1
  refine ⟨boolBernoulli_tail m k p, binomialTail_le_choose_pow m k p hp hp1, ?_⟩
  obtain ⟨hchoose, hfactorial⟩ := h03 m k hk
  have hpownonneg : 0 ≤ p ^ k := pow_nonneg hp k
  calc
    (m.choose k : ℝ) * p ^ k ≤ ((m : ℝ) ^ k / (k.factorial : ℝ)) * p ^ k :=
      mul_le_mul_of_nonneg_right hchoose hpownonneg
    _ ≤ ((Real.exp 1 * (m : ℝ) / k) ^ k) * p ^ k :=
      mul_le_mul_of_nonneg_right hfactorial hpownonneg
    _ = (Real.exp 1 * (m : ℝ) * p / k) ^ k := by
      rw [← mul_pow]
      congr 1
      ring

end ThLean.W.S651

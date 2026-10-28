import ThLean.BP.SA.Convergence

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA09

open ThLean.BP.SA
open ThresholdFoundations

private theorem binomialWeight_sum (B : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (B + 1), binomialWeight B p k) = 1 := by
  calc
    (∑ k ∈ Finset.range (B + 1), binomialWeight B p k) =
        ∑ k ∈ Finset.range (B + 1),
          (B.choose k : ℝ) * p ^ k * (1 - p) ^ (B - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkB : k ≤ B := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      simp [binomialWeight, hkB]
    _ = ∑ k ∈ Finset.range (B + 1),
          p ^ k * (1 - p) ^ (B - k) * (B.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (p + (1 - p)) ^ B := by rw [add_pow]
    _ = 1 := by ring

private theorem binomialEvent_le_gt_sum (B m : ℕ) (p : ℝ) :
    binomialEvent B p (fun k => k ≤ m) +
      binomialEvent B p (fun k => m < k) = 1 := by
  have hsplit :
      binomialEvent B p (fun k => k ≤ m) +
          binomialEvent B p (fun k => m < k) =
        ∑ k ∈ Finset.range (B + 1), binomialWeight B p k := by
    unfold binomialEvent
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkm : k ≤ m
    · simp [indicator, hkm]
    · have hmk : m < k := Nat.lt_of_not_ge hkm
      simp [indicator, hkm, hmk]
  rw [hsplit, binomialWeight_sum]

private theorem cutoff_valid_eventually (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, Nat.floor (c * n) ≤ n.choose 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * c + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnreal : 2 * c + 1 < (n : ℝ) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hchoose : c * (n : ℝ) ≤ (n.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfactor : 2 * c ≤ (n : ℝ) - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hfactor hn_nonneg]
  exact Nat.floor_le_of_le hchoose

/-- The lower sparse-binomial law, from the four transfer and probability leaves. -/
theorem SA_C65aStatement_of_deps
    (h55 : SA_X55Statement) (h58 : SA_X58bStatement)
    (h59 : SA_X59bStatement) (h00 : SA_F00Statement) :
    SA_C65aStatement := by
  intro q hq α hα hsimple d hd hdα
  have hhalf : d / 2 < α := by linarith
  obtain ⟨c, hdc, hcα⟩ := exists_between hhalf
  have hc0 : 0 ≤ c := by linarith
  have hsimple : Tendsto
      (fun n : ℕ => simpleProbability (V := Fin n) q (Nat.floor (c * n)))
      atTop (𝓝 1) := hsimple.1 c hc0 hcα
  have htail := h58 d hd |>.1 c hdc
  let weak : ℕ → ℝ := fun n =>
    binomialEvent (n.choose 2) (d / n) (fun k => k ≤ Nat.floor (c * n))
  let tail : ℕ → ℝ := fun n =>
    binomialEvent (n.choose 2) (d / n) (fun k => Nat.floor (c * n) < k)
  have hweak : Tendsto weak atTop (𝓝 1) := by
    have hlimit : Tendsto (fun n : ℕ => 1 - tail n) atTop (𝓝 1) := by
      simpa [tail] using tendsto_const_nhds.sub htail
    apply hlimit.congr'
    filter_upwards [] with n
    have heq := binomialEvent_le_gt_sum (n.choose 2) (Nat.floor (c * n)) (d / n)
    dsimp [weak, tail]
    linarith
  have hproduct : Tendsto
      (fun n : ℕ =>
        simpleProbability (V := Fin n) q (Nat.floor (c * n)) * weak n)
      atTop (𝓝 1) := by
    simpa using hsimple.mul hweak
  have hvalid : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 0 < n ∧ d ≤ (n : ℝ) ∧
        Nat.floor (c * n) ≤ n.choose 2 := by
    filter_upwards [eventually_ge_atTop 2, h59 d hd, cutoff_valid_eventually c]
      with n hn2 hdom hcut
    exact ⟨hn2, hdom.1, hdom.2, hcut⟩
  have hlow : ∀ᶠ n : ℕ in atTop,
      simpleProbability (V := Fin n) q (Nat.floor (c * n)) * weak n ≤
        bernoulliProbability (V := Fin n) q (d / n) := by
    filter_upwards [hvalid] with n hn
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn.2.1
    have hprob0 : 0 ≤ d / (n : ℝ) := div_nonneg hd hnpos.le
    have hprob1 : d / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnpos]
      exact hn.2.2.1
    have hbound := h55 q n (Nat.floor (c * n)) (by omega) hn.1
      hn.2.2.2 (d / (n : ℝ)) hprob0 hprob1
    simpa [weak] using hbound.1
  have hupper : ∀ᶠ n : ℕ in atTop,
      bernoulliProbability (V := Fin n) q (d / n) ≤ 1 := by
    filter_upwards [hvalid] with n hn
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn.2.1
    have hprob0 : 0 ≤ d / (n : ℝ) := div_nonneg hd hnpos.le
    have hprob1 : d / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnpos]
      exact hn.2.2.1
    exact (h00.2.2.2 q n (by omega) hn.1 (d / (n : ℝ)) hprob0 hprob1).2
  have hbernoulli : Tendsto
      (fun n : ℕ => bernoulliProbability (V := Fin n) q (d / n))
      atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hproduct tendsto_const_nhds
      hlow hupper
  have hdomain : ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 ≤ d ∧ d ≤ (n : ℝ) := by
    filter_upwards [h59 d hd] with n hn
    exact ⟨hn.1, hd, hn.2⟩
  have hsparse : Tendsto (fun n : ℕ => sparseProbability q n d) atTop (𝓝 1) := by
    apply hbernoulli.congr'
    filter_upwards [hdomain] with n hn
    simp [sparseProbability, hn.1, hn.2]
  exact hsparse

end ThLean.W.SA09

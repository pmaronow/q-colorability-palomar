module

public import ThLean.BP.SA.Transfer
public import ThLean.BP.SA.Basics

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA73

open ThresholdFoundations ThLean.BP.SA

/-- The binomial mixture comparison, given fixed-size monotonicity, the mixture
formula, and the finite probability bounds. -/
theorem SA_X55Statement_of_deps
    (h53 : SA_X53Statement) (h54 : SA_X54Statement)
    (hF00 : SA_F00Statement) : SA_X55Statement := by
  intro q n m hq hn hm p hp0 hp1
  let B : ℕ := n.choose 2
  let w : ℕ → ℝ := fun j => binomialWeight B p j
  let s : ℕ → ℝ := fun j => simpleProbability (V := Fin n) q j
  have hmixture := h54 q n hq hn p hp0 hp1
  have hmix : bernoulliProbability (V := Fin n) q p =
      ∑ j ∈ Finset.range (B + 1), w j * s j := by
    simpa [B, w, s] using hmixture.1
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    simpa [w, B] using hmixture.2.1 j
  have hwsum : (∑ j ∈ Finset.range (B + 1), w j) = 1 := by
    simpa [w, B] using hmixture.2.2
  have hsBound := hF00.2.2.1
  have hs_m : 0 ≤ s m ∧ s m ≤ 1 := by
    simpa [s] using hsBound q n m hq hn hm
  have hs_range : ∀ j ≤ B, 0 ≤ s j ∧ s j ≤ 1 := by
    intro j hj
    exact hsBound q n j hq hn hj

  have hLowerTerm : ∀ j ∈ Finset.range (B + 1),
      s m * (w j * indicator (j ≤ m)) ≤ w j * s j := by
    intro j hj
    have hjB : j ≤ B := by
      have hj' : j < B + 1 := Finset.mem_range.mp hj
      omega
    by_cases hjm : j ≤ m
    · have hmono := h53 q n j m hq hn hjm hm
      have hmul := mul_le_mul_of_nonneg_left hmono (hw j)
      simpa [w, s, indicator, hjm, mul_comm] using hmul
    · have hnonneg := mul_nonneg (hw j) (hs_range j hjB).1
      simpa [w, s, indicator, hjm] using hnonneg

  have hLowerSum : s m * binomialEvent B p (fun j => j ≤ m) ≤
      ∑ j ∈ Finset.range (B + 1), w j * s j := by
    calc
      s m * binomialEvent B p (fun j => j ≤ m) =
          ∑ j ∈ Finset.range (B + 1), s m * (w j * indicator (j ≤ m)) := by
        simp [binomialEvent, w, Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range (B + 1), w j * s j := by
        simpa [w, s] using Finset.sum_le_sum hLowerTerm

  have hUpperTerm : ∀ j ∈ Finset.range (B + 1),
      w j * s j ≤ w j * s m + w j * indicator (j < m) := by
    intro j hj
    have hjB : j ≤ B := by
      have hj' : j < B + 1 := Finset.mem_range.mp hj
      omega
    by_cases hjm : j < m
    · have hsj := (hs_range j hjB).2
      have hmul := mul_le_mul_of_nonneg_left hsj (hw j)
      have hnonneg := mul_nonneg (hw j) hs_m.1
      have hmain : w j * s j ≤ w j := by nlinarith [hmul]
      have hadd : w j ≤ w j * s m + w j := by nlinarith [hnonneg]
      simpa [indicator, hjm] using le_trans hmain hadd
    · have hmj : m ≤ j := by omega
      have hmono := h53 q n m j hq hn hmj hjB
      have hmul := mul_le_mul_of_nonneg_left hmono (hw j)
      simpa [w, s, indicator, hjm] using hmul

  have hUpperSum :
      (∑ j ∈ Finset.range (B + 1), w j * s j) ≤
        s m + binomialEvent B p (fun j => j < m) := by
    calc
      (∑ j ∈ Finset.range (B + 1), w j * s j) ≤
          ∑ j ∈ Finset.range (B + 1),
            (w j * s m + w j * indicator (j < m)) := by
        exact Finset.sum_le_sum hUpperTerm
      _ = (∑ j ∈ Finset.range (B + 1), w j) * s m +
            binomialEvent B p (fun j => j < m) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp [binomialEvent, w]
      _ = s m + binomialEvent B p (fun j => j < m) := by
        rw [hwsum]
        simp

  constructor
  · rw [hmix]
    simpa [w, s, B] using hLowerSum
  · rw [hmix]
    simpa [w, s, B] using hUpperSum

end ThLean.W.SA73

import ThLean.BP.S4.Parameters

noncomputable section

open Filter
open scoped BigOperators Topology ENNReal
open ThresholdFoundations

namespace ThLean.W.S430

theorem S4_PAR_05Statement_of_deps
    (h04 : ThLean.BP.S4.S4_PAR_04Statement) :
    ThLean.BP.S4.S4_PAR_05Statement := by
  unfold ThLean.BP.S4.S4_PAR_05Statement
  have hraw : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-(3 : ℝ) / 2)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hmajor : Summable (fun k : ℕ => Real.rpow (k + 1 : ℝ) (-(3 : ℝ) / 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff
        (f := fun n : ℕ => Real.rpow (n : ℝ) (-(3 : ℝ) / 2)) 1).2 hraw
  have hnonneg : ∀ n : ℕ, 0 ≤ epsilon n := by
    intro n
    unfold epsilon
    split_ifs with hn
    · positivity
    · apply Real.rpow_nonneg
      have hn1 : 1 < n := by omega
      exact le_of_lt (Real.log_pos (by exact_mod_cast hn1))
  have hbound (k : ℕ) :
      epsilon (Nat.floor (Real.exp ((((k + 1 : ℕ) : ℝ) + 1)))) ≤
        Real.rpow (k + 1 : ℝ) (-(3 : ℝ) / 2) := by
    have hk := h04 (k + 2) (by omega)
    have harg : (((k + 1 : ℕ) : ℝ) + 1) = ((k + 2 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [harg]
    calc
      epsilon (Nat.floor (Real.exp ((k + 2 : ℕ) : ℝ))) ≤
          Real.rpow (((k + 2 : ℕ) : ℝ) - 1) (-(3 : ℝ) / 2) := hk.2.2
      _ = Real.rpow (k + 1 : ℝ) (-(3 : ℝ) / 2) := by
        congr 1
        push_cast
        ring
  have hshift :
      Summable (fun k : ℕ =>
        epsilon (Nat.floor (Real.exp ((((k + 1 : ℕ) : ℝ) + 1)))) ) :=
    Summable.of_nonneg_of_le (fun k => hnonneg _) hbound hmajor
  exact (summable_nat_add_iff
    (f := fun k : ℕ => epsilon (Nat.floor (Real.exp (k + 1 : ℝ)))) 1).1 hshift

example (h04 : ThLean.BP.S4.S4_PAR_04Statement) :
    ThLean.BP.S4.S4_PAR_05Statement := S4_PAR_05Statement_of_deps h04

end ThLean.W.S430

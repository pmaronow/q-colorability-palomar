import ThLean.BP.S5.Elementary
import Mathlib.Data.Nat.Choose.Multinomial

noncomputable section
open scoped BigOperators
open ThresholdFoundations

namespace ThLean.W.S512

theorem poissonWeight_piAntidiag {A : Type*} [Fintype A] [DecidableEq A]
    (r : A → ℝ) (m : ℕ) :
    (∑ x ∈ Finset.piAntidiag Finset.univ m,
      ∏ i, poissonWeight (r i) (x i)) =
      poissonWeight (∑ i, r i) m := by
  classical
  let R : ℝ := ∑ i, r i
  have hfac (x : A → ℕ) (hx : x ∈ Finset.piAntidiag Finset.univ m) :
      (∏ i, ((x i).factorial : ℝ)) *
        (Nat.multinomial Finset.univ x : ℝ) = (m.factorial : ℝ) := by
    have hs := (Finset.mem_piAntidiag.mp hx).1
    have h := Nat.multinomial_spec (s := Finset.univ) (f := x)
    rw [hs] at h
    exact_mod_cast h
  have hterm (x : A → ℕ) (hx : x ∈ Finset.piAntidiag Finset.univ m) :
      (∏ i, poissonWeight (r i) (x i)) =
        Real.exp (-R) *
          ((Nat.multinomial Finset.univ x : ℝ) * (∏ i, r i ^ x i)) /
            (m.factorial : ℝ) := by
    have hprod : (∏ i, poissonWeight (r i) (x i)) =
        Real.exp (-R) * (∏ i, r i ^ x i) /
          (∏ i, ((x i).factorial : ℝ)) := by
      simp [poissonWeight, R, Finset.prod_mul_distrib, Finset.prod_div_distrib,
        ← Real.exp_sum]
    rw [hprod]
    have hb : (∏ i, ((x i).factorial : ℝ)) ≠ 0 := by positivity
    have hm : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    rw [← hfac x hx]
    ring
  calc
    (∑ x ∈ Finset.piAntidiag Finset.univ m,
        ∏ i, poissonWeight (r i) (x i)) =
        Real.exp (-R) *
          ((∑ x ∈ Finset.piAntidiag Finset.univ m,
              (Nat.multinomial Finset.univ x : ℝ) * (∏ i, r i ^ x i)) /
            (m.factorial : ℝ)) := by
      rw [Finset.sum_congr rfl (fun x hx => hterm x hx)]
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      rw [← Finset.mul_sum]
    _ = Real.exp (-R) * (R ^ m / (m.factorial : ℝ)) := by
      rw [Finset.sum_pow_eq_sum_piAntidiag]
    _ = poissonWeight R m := by
      simp [poissonWeight, R]
      ring

end ThLean.W.S512

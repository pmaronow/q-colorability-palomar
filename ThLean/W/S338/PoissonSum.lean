import ThLean.BP.S3.Poisson
import Mathlib.Data.Nat.Choose.Multinomial

noncomputable section
open scoped BigOperators

namespace ThLean.W.S338

open ThresholdFoundations

private lemma finite_sum_index {J : Type*} [Fintype J] (k : ℕ) :
    {c : J → ℕ | (∑ j, c j) = k}.Finite := by
  apply Set.Finite.subset (s := Set.univ.pi fun _ : J => Set.Iic k)
  · exact Set.Finite.pi fun _ => Set.finite_Iic k
  · intro c hc
    simp only [Set.mem_ofPred_eq] at hc
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]
    intro j
    calc
      c j ≤ ∑ i : J, c i := Finset.single_le_sum (fun i hi => Nat.zero_le (c i))
        (Finset.mem_univ j)
      _ = k := hc

private lemma poissonWeight_prod_eq {J : Type*} [Fintype J]
    (rate : J → ℝ) (c : J → ℕ) :
    (∏ j, poissonWeight (rate j) (c j)) =
      Real.exp (-(∑ j, rate j)) *
        (∏ j, rate j ^ c j) / (∏ j, (Nat.factorial (c j) : ℝ)) := by
  simp only [poissonWeight]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 1
  simp [Finset.sum_neg_distrib]

private lemma poissonWeight_sum_fixed_total {J : Type*} [Fintype J]
    (rate : J → ℝ) (k : ℕ) :
    (∑' c : J → ℕ, if (∑ j, c j) = k then ∏ j, poissonWeight (rate j) (c j) else 0) =
      poissonWeight (∑ j, rate j) k := by
  classical
  let s : Finset J := Finset.univ
  let A : Finset (J → ℕ) := Finset.piAntidiag s k
  have hsum :
      (∑' c : J → ℕ, if (∑ j, c j) = k then ∏ j, poissonWeight (rate j) (c j) else 0) =
        ∑ c ∈ A, ∏ j, poissonWeight (rate j) (c j) := by
    rw [tsum_eq_sum (s := A)]
    · apply Finset.sum_congr rfl
      intro c hc
      have heq : (∑ j, c j) = k := by
        simpa [s] using (Finset.mem_piAntidiag.mp hc).1
      simp [heq]
    · intro c hc
      have hne : (∑ j, c j) ≠ k := by
        intro htotal
        apply hc
        apply Finset.mem_piAntidiag.mpr
        constructor
        · simpa [s] using htotal
        · simp [s]
      simp [hne]
  have hfactor (c : J → ℕ) (hc : c ∈ A) :
      (Nat.multinomial s c : ℝ) * (∏ j, rate j ^ c j) / (k.factorial : ℝ) =
        ∏ j, rate j ^ c j / ((Nat.factorial (c j) : ℝ)) := by
    have hc' := Finset.mem_piAntidiag.mp hc
    have hspec :
        (∏ j, ((c j).factorial : ℝ)) * (Nat.multinomial s c : ℝ) =
          (k.factorial : ℝ) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.multinomial_spec s c)
      simpa [s, hc'.1] using h
    have hmulti : (Nat.multinomial s c : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.multinomial_pos s c).ne'
    have hfac : (∏ j, ((c j).factorial : ℝ)) ≠ 0 := by
      positivity
    rw [Finset.prod_div_distrib]
    rw [← hspec]
    field_simp [hmulti, hfac]
  have hcoeff :
      (∑ c ∈ A, (Nat.multinomial s c : ℝ) * ∏ j, rate j ^ c j) =
        (∑ j, rate j) ^ k := by
    simpa [A, s] using (Finset.sum_pow_eq_sum_piAntidiag (s := s) (f := rate) k).symm
  calc
    _ = ∑ c ∈ A, ∏ j, poissonWeight (rate j) (c j) := hsum
    _ = ∑ c ∈ A,
          Real.exp (-(∑ j, rate j)) *
            ((Nat.multinomial s c : ℝ) * (∏ j, rate j ^ c j) / (k.factorial : ℝ)) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [poissonWeight_prod_eq]
          rw [hfactor c hc]
          rw [Finset.prod_div_distrib]
          ring
    _ = Real.exp (-(∑ j, rate j)) *
          ((∑ c ∈ A, (Nat.multinomial s c : ℝ) * ∏ j, rate j ^ c j) /
            (k.factorial : ℝ)) := by
          simp_rw [div_eq_mul_inv]
          calc
            _ = (Real.exp (-(∑ j, rate j)) * (k.factorial : ℝ)⁻¹) *
                  ∑ c ∈ A, (Nat.multinomial s c : ℝ) * ∏ j, rate j ^ c j := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro c hc
                    ring
            _ = _ := by ring
    _ = Real.exp (-(∑ j, rate j)) * ((∑ j, rate j) ^ k / (k.factorial : ℝ)) := by
          rw [hcoeff]
    _ = poissonWeight (∑ j, rate j) k := by
          rw [poissonWeight]
          ring

theorem S3_36SStatement_holds : ThLean.BP.S3.S3_36SStatement := by
  intro J inst rate hr k
  constructor
  · classical
    apply summable_of_hasFiniteSupport
    apply (finite_sum_index k).subset
    intro c hc
    change (if (∑ j, c j) = k then ∏ j, poissonWeight (rate j) (c j) else 0) ≠ 0 at hc
    have htotal : (∑ j, c j) = k := by
      by_contra htotal
      apply hc
      simp [htotal]
    exact htotal
  · exact poissonWeight_sum_fixed_total rate k

example : ThLean.BP.S3.S3_36SStatement := S3_36SStatement_holds

end ThLean.W.S338

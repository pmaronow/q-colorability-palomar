module

public import ThLean.BP.SA.Interpolation
public import Mathlib.Algebra.MvPolynomial.Coeff

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA20S
open ThresholdFoundations

/-- Group a tuple product by the multiplicities of its entries. -/
theorem prod_tuple_counts {D M : Type*} [Fintype D] [DecidableEq D] [CommMonoid M]
    (f : D → M) {k : ℕ} (x : Fin k → D) :
    (∏ i, f (x i)) = ∏ e, f e ^ (List.ofFn x).count e := by
  calc
    (∏ i, f (x i)) = ((List.ofFn x).map f).prod := by
      simp [List.map_ofFn, List.prod_ofFn]
    _ = ∏ e ∈ (List.ofFn x).toFinset, f e ^ (List.ofFn x).count e :=
      Finset.prod_list_map_count _ _
    _ = ∏ e, f e ^ (List.ofFn x).count e := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro e _ he
      simp only [List.mem_toFinset] at he
      rw [List.count_eq_zero_of_not_mem he, pow_zero]

/-- A tuple's monomial coefficient records exactly its histogram. -/
theorem coeff_tuple_product {D : Type*} [Fintype D] [DecidableEq D]
    (ν : D → ℝ) {k : ℕ} (x : Fin k → D) (z : D →₀ ℕ) :
    (∏ i, ν (x i) • MvPolynomial.X (x i)).coeff z =
      (∏ i, ν (x i)) * indicator (∀ e, (List.ofFn x).count e = z e) := by
  simp_rw [MvPolynomial.smul_eq_C_mul]
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.coeff_C_mul,
    prod_tuple_counts (MvPolynomial.X : D → MvPolynomial D ℝ),
    MvPolynomial.coeff_prod_X_pow]
  congr 1
  simp only [indicator]
  congr 1
  simp only [Finsupp.ext_iff, Finsupp.indicator_apply, Finset.mem_univ, ↓reduceDIte,
    eq_comm]

/-- The multinomial coefficient formula applied to the histogram of a tuple. -/
theorem weighted_histogram_multinomial {D : Type*} [Fintype D] [DecidableEq D]
    (ν : D → ℝ) (k : ℕ) (z : D →₀ ℕ) :
    (∑ x : Fin k → D,
      (∏ i, ν (x i)) * indicator (∀ e, (List.ofFn x).count e = z e)) =
    if (∑ e, z e) = k then
      (Nat.multinomial Finset.univ z : ℝ) * ∏ e, ν e ^ z e else 0 := by
  have h := MvPolynomial.coeff_linearCombination_X_pow_of_fintype ν z k
  rw [Fintype.sum_pow, MvPolynomial.coeff_sum] at h
  simp_rw [coeff_tuple_product] at h
  rw [z.sum_fintype (fun _ m => m) (by simp),
    z.prod_fintype (fun e m => ν e ^ m) (by simp),
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at h
  exact h

theorem real_multinomial {D : Type*} [Fintype D] (z : D → ℕ) :
    (Nat.multinomial Finset.univ z : ℝ) =
      (Nat.factorial (∑ e, z e) : ℝ) / ∏ e, (Nat.factorial (z e) : ℝ) := by
  have hp : (∏ e, (Nat.factorial (z e) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)
  apply (eq_div_iff hp).2
  have h := Nat.multinomial_spec Finset.univ z
  exact_mod_cast (by simpa [mul_comm] using h)

/-- Weighted count of all tuples with a prescribed histogram; weights may be signed. -/
theorem weighted_histogram {D : Type*} [Fintype D] [DecidableEq D]
    (ν : D → ℝ) (k : ℕ) (z : D → ℕ) :
    (∑ x : Fin k → D,
      (∏ i, ν (x i)) * indicator (∀ e, (List.ofFn x).count e = z e)) =
      if (∑ e, z e) = k then
        ((Nat.factorial k : ℝ) / ∏ e, (Nat.factorial (z e) : ℝ)) *
          ∏ e, ν e ^ z e
      else 0 := by
  have h := weighted_histogram_multinomial ν k (Finsupp.equivFunOnFinite.symm z)
  simp only [Finsupp.coe_equivFunOnFinite_symm, real_multinomial] at h
  by_cases hz : (∑ e, z e) = k
  · simpa only [hz, ite_true] using h
  · simpa only [hz, ite_false] using h

/-- Factor the Poisson histogram coefficient, algebraically for real means. -/
theorem poisson_product_factor {D : Type*} [Fintype D]
    (ν : D → ℝ) (μ : ℝ) (z : D → ℕ) (hsum : (∑ e, ν e) = 1) :
    poissonWeight μ (∑ e, z e) *
      (((Nat.factorial (∑ e, z e) : ℝ) /
        ∏ e, (Nat.factorial (z e) : ℝ)) * ∏ e, ν e ^ z e) =
      ∏ e, poissonWeight (μ * ν e) (z e) := by
  have hexp : (∏ e, Real.exp (-(μ * ν e))) = Real.exp (-μ) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hsum, mul_one]
  have hpow : (∏ e, (μ * ν e) ^ z e) = μ ^ (∑ e, z e) * ∏ e, ν e ^ z e := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hfac : (Nat.factorial (∑ e, z e) : ℝ) ≠ 0 := by positivity
  simp only [poissonWeight, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [hexp, hpow]
  field_simp

end ThLean.W.SA20S

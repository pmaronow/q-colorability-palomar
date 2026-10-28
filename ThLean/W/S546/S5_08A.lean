import ThLean.BP.S5.Poisson

noncomputable section
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S546

open ThresholdFoundations
open ThLean.BP.S5

private lemma sum_histogram_counts {E : Type} [Fintype E] (m : ℕ)
    (x : Fin m → E) :
    (∑ e : E, (Finset.univ.filter (fun i : Fin m => x i = e)).card) = m := by
  classical
  have hcard :
      (Finset.univ : Finset (Fin m)).card =
        ∑ e ∈ (Finset.univ : Finset E),
          (Finset.univ.filter (fun i : Fin m => x i = e)).card := by
    exact Finset.card_eq_sum_card_fiberwise (f := x) (s := Finset.univ)
      (t := Finset.univ) (by intro i hi; exact Finset.mem_univ _)
  simpa using hcard.symm

private lemma uniformProb_histogram_zero_of_ne_total
    {E : Type} [Fintype E] [Nonempty E] (m : ℕ) (c : E → ℕ)
    (hm : m ≠ ∑ e, c e) :
    uniformProb (fun x : Fin m → E =>
      ∀ e, (Finset.univ.filter (fun i => x i = e)).card = c e) = 0 := by
  classical
  have hnot (x : Fin m → E) :
      ¬ ∀ e, (Finset.univ.filter (fun i => x i = e)).card = c e := by
    intro hx
    have hcounts := sum_histogram_counts m x
    have htotal : m = ∑ e, c e := by
      calc
        m = ∑ e : E, (Finset.univ.filter (fun i : Fin m => x i = e)).card := hcounts.symm
        _ = ∑ e : E, c e := by
          apply Finset.sum_congr rfl
          intro e he
          exact hx e
    exact hm htotal
  simp [uniformProb, uniformMean, indicator, hnot]

private lemma poisson_histogram_product_identity
    {E : Type} [Fintype E] [Nonempty E] (t : ℝ) (c : E → ℕ) :
    poissonWeight t (∑ e, c e) *
      (((∑ e, c e).factorial : ℝ) /
        ((Fintype.card E : ℝ) ^ (∑ e, c e) *
          ∏ e, ((c e).factorial : ℝ))) =
      ∏ e, poissonWeight (t / Fintype.card E) (c e) := by
  classical
  let M : ℕ := ∑ e, c e
  let N : ℝ := Fintype.card E
  let D : ℝ := ∏ e, ((c e).factorial : ℝ)
  have hNnat : 0 < Fintype.card E := Fintype.card_pos
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (Nat.ne_of_gt hNnat)
  have hfact (e : E) : ((c e).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (c e))
  have hD : D ≠ 0 := by
    dsimp [D]
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    exact hfact e
  have hexp : (∏ e : E, Real.exp (-(t / N))) = Real.exp (-t) := by
    rw [← Real.exp_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    dsimp [N]
    field_simp [hN]
  have hpow : (∏ e : E, (t / N) ^ c e) = (t / N) ^ M := by
    dsimp [M]
    exact Finset.prod_pow_eq_pow_sum Finset.univ c (t / N)
  calc
    poissonWeight t M *
        ((M.factorial : ℝ) / (N ^ M * D)) =
        Real.exp (-t) * (t / N) ^ M / D := by
          simp only [poissonWeight]
          dsimp [D]
          field_simp [hN, hD, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)]
          rw [div_pow]
          field_simp [hN]
    _ = (∏ e : E, Real.exp (-(t / N))) *
          (∏ e : E, (t / N) ^ c e) / D := by rw [hexp, hpow]
    _ = ∏ e : E, poissonWeight (t / N) (c e) := by
          symm
          calc
            (∏ e : E, poissonWeight (t / N) (c e)) =
                (∏ e : E, (Real.exp (-(t / N)) * (t / N) ^ c e)) / D := by
                  simp_rw [poissonWeight]
                  rw [Finset.prod_div_distrib]
            _ = ((∏ e : E, Real.exp (-(t / N))) *
                  (∏ e : E, (t / N) ^ c e)) / D := by
                  rw [Finset.prod_mul_distrib]
            _ = (∏ e : E, Real.exp (-(t / N))) *
                  (∏ e : E, (t / N) ^ c e) / D := rfl

theorem S5_08AStatement_of_deps
    (hE02 : ThLean.BP.S5.S5_E02Statement) :
    ThLean.BP.S5.S5_08AStatement := by
  intro E _ hE t ht c
  let M : ℕ := ∑ e, c e
  let R : ℝ := ∏ e, poissonWeight (t / Fintype.card E) (c e)
  have hprob := hE02.2 E c
  have hterm : ∀ m : ℕ,
      poissonWeight t m *
          uniformProb (fun x : Fin m → E =>
            ∀ e, (Finset.univ.filter (fun i => x i = e)).card = c e) =
        if m = M then R else 0 := by
    intro m
    by_cases hm : m = M
    · subst m
      rw [if_pos rfl, hprob]
      simpa [M, R] using poisson_histogram_product_identity t c
    · have hzero := uniformProb_histogram_zero_of_ne_total m c (by simpa [M] using hm)
      simp [hm, M, R, hzero]
  have hsum : HasSum (fun m : ℕ => if m = M then R else 0) R := hasSum_ite_eq M R
  simpa only [hterm] using hsum

end ThLean.W.S546

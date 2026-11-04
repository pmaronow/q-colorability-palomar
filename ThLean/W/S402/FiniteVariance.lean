module

public import ThLean.BP.S4.Finite

@[expose] public section

noncomputable section

open scoped BigOperators

namespace ThLean.W.S402

open ThresholdFoundations

private theorem uniformMean_add {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp only [uniformMean, Finset.sum_add_distrib]
  exact add_div _ _ _

private theorem uniformMean_sub {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp only [uniformMean, Finset.sum_sub_distrib]
  exact sub_div _ _ _

private theorem uniformMean_scale {A : Type} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean]
  rw [← mul_div_assoc, ← Finset.mul_sum]

private theorem uniformMean_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  unfold uniformMean
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  field_simp

private theorem uniformMean_prod {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  simp only [uniformMean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  conv_rhs => rw [← Finset.sum_div]
  field_simp

private theorem uniformMean_centered_zero {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    uniformMean (fun a => f a - uniformMean f) = 0 := by
  rw [uniformMean_sub, uniformMean_const]
  ring

private theorem variance_eq_mean_sq_sub {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    variance f = uniformMean (fun a => (f a)^2) - (uniformMean f)^2 := by
  let μ := uniformMean f
  have hexp : (fun a => (f a - μ)^2) =
      (fun a => (f a)^2 - (2 * μ) * f a + μ^2) := by
    funext a
    ring
  calc
    variance f = uniformMean (fun a => (f a - μ)^2) := by
      simp [variance, μ]
    _ = uniformMean (fun a => (f a)^2 - (2 * μ) * f a + μ^2) :=
      congrArg uniformMean hexp
    _ = uniformMean (fun a => (f a)^2) - (2 * μ) * uniformMean f + μ^2 := by
      rw [uniformMean_add, uniformMean_sub, uniformMean_scale, uniformMean_const]
    _ = uniformMean (fun a => (f a)^2) - (uniformMean f)^2 := by
      dsimp [μ]
      ring

private theorem variance_nonneg {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) : 0 ≤ variance f := by
  unfold variance uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg fun a _ => sq_nonneg _
  · exact Nat.cast_nonneg _

private theorem pair_sq_mean {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    uniformMean (fun p : A × A => (f p.1 - f p.2)^2) =
      2 * (uniformMean (fun a => (f a)^2) - (uniformMean f)^2) := by
  let μ := uniformMean f
  let m₂ := uniformMean (fun a => (f a)^2)
  have hinner (a : A) :
      uniformMean (fun b => (f a - f b)^2) = (f a)^2 - (2 * μ) * f a + m₂ := by
    have hexp : (fun b => (f a - f b)^2) =
        (fun b => (f a)^2 - (2 * f a) * f b + (f b)^2) := by
      funext b
      ring
    rw [hexp, uniformMean_add, uniformMean_sub, uniformMean_const,
      uniformMean_scale]
    dsimp [μ, m₂]
    ring
  have houter :
      uniformMean (fun a => uniformMean (fun b => (f a - f b)^2)) =
        2 * (uniformMean (fun a => (f a)^2) - (uniformMean f)^2) := by
    calc
      uniformMean (fun a => uniformMean (fun b => (f a - f b)^2)) =
          uniformMean (fun a => (f a)^2 - (2 * μ) * f a + m₂) := by
        congr 1
        funext a
        exact hinner a
      _ = uniformMean (fun a => (f a)^2) - (2 * μ) * uniformMean f + m₂ := by
        rw [uniformMean_add, uniformMean_sub, uniformMean_scale, uniformMean_const]
      _ = 2 * (uniformMean (fun a => (f a)^2) - (uniformMean f)^2) := by
        dsimp [μ, m₂]
        ring
  calc
    uniformMean (fun p : A × A => (f p.1 - f p.2)^2) =
        uniformMean (fun a => uniformMean (fun b => (f a - f b)^2)) := by
      exact uniformMean_prod (fun p : A × A => (f p.1 - f p.2)^2)
    _ = 2 * (uniformMean (fun a => (f a)^2) - (uniformMean f)^2) := houter

theorem S4_ES_01Statement_holds : ThLean.BP.S4.S4_ES_01Statement := by
  intro A _ hA f c
  have hfirst :
      uniformMean (fun a => (f a - c)^2) = variance f + (uniformMean f - c)^2 := by
    let μ := uniformMean f
    have hexp : (fun a => (f a - c)^2) =
        (fun a => (f a - μ)^2 + (2 * (μ - c)) * (f a - μ) + (μ - c)^2) := by
      funext a
      ring
    calc
      uniformMean (fun a => (f a - c)^2) =
          uniformMean (fun a => (f a - μ)^2 +
            (2 * (μ - c)) * (f a - μ) + (μ - c)^2) := congrArg uniformMean hexp
      _ = variance f + (uniformMean f - c)^2 := by
        rw [uniformMean_add, uniformMean_add, uniformMean_scale,
          uniformMean_centered_zero, uniformMean_const]
        simp only [variance]
        dsimp [μ]
        ring
  refine ⟨hfirst, ?_, ?_⟩
  · have hp := pair_sq_mean f
    have hv := variance_eq_mean_sq_sub f
    calc
      variance f = (1 / 2 : ℝ) *
          (2 * (uniformMean (fun a => (f a)^2) - (uniformMean f)^2)) := by
        rw [hv]
        ring
      _ = (1 / 2 : ℝ) *
          uniformMean (fun p : A × A => (f p.1 - f p.2)^2) := by
        rw [hp]
  · have hv := variance_nonneg f
    have hvar := variance_eq_mean_sq_sub f
    nlinarith

end ThLean.W.S402

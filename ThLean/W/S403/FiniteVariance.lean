import ThLean.BP.S4.Finite

/-!
The finite-average helpers `uniformMean_sub_const_sq`
match implementation patterns in OpenAI's math library (Apache-2.0).
Local versions use project-specific averaging definitions and namespaces.
Their source credits and licence scope are listed in NOTICE; the licence
text is in LICENSES/Apache-2.0.txt.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S403
open ThresholdFoundations

private lemma uniformMean_add {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun x => f x + g x) = uniformMean f + uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_add_distrib]
  ring

private lemma uniformMean_sub {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun x => f x - g x) = uniformMean f - uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_sub_distrib]
  ring

private lemma uniformMean_const_mul {A : Type} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun x => c * f x) = c * uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

private lemma uniformMean_mul_const {A : Type} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun x => f x * c) = uniformMean f * c := by
  unfold uniformMean
  rw [← Finset.sum_mul]
  ring

private lemma uniformMean_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  unfold uniformMean
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

private lemma uniformMean_fubini {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a, b))) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Finset.sum_div]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hA, hB]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  field_simp [hA, hB]
  rw [Nat.cast_mul]
  ring

private lemma uniformMean_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [Equiv.sum_comp e, Fintype.card_congr e]

private lemma uniformMean_fubini_swap {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean (fun a => uniformMean (fun b => f (a, b))) =
      uniformMean (fun b => uniformMean (fun a => f (a, b))) := by
  calc
    uniformMean (fun a => uniformMean (fun b => f (a, b))) = uniformMean f :=
      (uniformMean_fubini f).symm
    _ = uniformMean (fun p : B × A => f (p.2, p.1)) := by
      simpa using uniformMean_equiv (Equiv.prodComm A B)
        (fun p : B × A => f (p.2, p.1))
    _ = uniformMean (fun b => uniformMean (fun a => f (a, b))) :=
      uniformMean_fubini (fun p : B × A => f (p.2, p.1))

private lemma uniformMean_mono {A : Type} [Fintype A] [Nonempty A]
    {f g : A → ℝ} (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  apply (div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) _)
  exact (le_of_lt (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < (Fintype.card A : ℝ)))

private lemma uniformMean_sq_le {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (uniformMean f) ^ 2 ≤ uniformMean (fun a => (f a) ^ 2) := by
  simpa only [uniformMean, Finset.card_univ] using
    (sum_div_card_sq_le_sum_sq_div_card (s := Finset.univ) (f := f))

private lemma uniformMean_sub_const_sq {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (c : ℝ) :
    uniformMean (fun x => (f x - c) ^ 2) =
      uniformMean (fun x => (f x) ^ 2) - 2 * c * uniformMean f + c ^ 2 := by
  have heq : (fun x => (f x - c) ^ 2) =
      fun x => (f x) ^ 2 - 2 * c * f x + c ^ 2 := by
    funext x
    ring
  rw [heq, uniformMean_add, uniformMean_sub, uniformMean_const_mul, uniformMean_const]

private lemma variance_eq_mean_sq_sub_sqmean {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    variance f = uniformMean (fun a => (f a) ^ 2) - (uniformMean f) ^ 2 := by
  unfold variance
  rw [uniformMean_sub_const_sq]
  ring

private lemma variance_two_copy {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) :
    variance f = (1 / 2 : ℝ) *
      uniformMean (fun p : A × A => (f p.1 - f p.2) ^ 2) := by
  have hrow (a : A) :
      uniformMean (fun b => (f a - f b) ^ 2) =
        uniformMean (fun b => (f b) ^ 2) - 2 * f a * uniformMean f + (f a) ^ 2 := by
    calc
      uniformMean (fun b => (f a - f b) ^ 2) =
          uniformMean (fun b => (f b - f a) ^ 2) := by
            congr 1
            funext b
            ring
      _ = _ := uniformMean_sub_const_sq f (f a)
  have hpair :
      uniformMean (fun p : A × A => (f p.1 - f p.2) ^ 2) =
        2 * uniformMean (fun a => (f a) ^ 2) - 2 * (uniformMean f) ^ 2 := by
    rw [uniformMean_fubini]
    simp_rw [hrow]
    rw [uniformMean_add, uniformMean_sub, uniformMean_mul_const,
      uniformMean_const_mul, uniformMean_const]
    ring
  rw [variance_eq_mean_sq_sub_sqmean, hpair]
  ring

private lemma uniformMean_variance {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean (fun a => variance (fun b => f (a, b))) =
      uniformMean (fun p : A × B => (f p) ^ 2) -
        uniformMean (fun a => (uniformMean (fun b => f (a, b))) ^ 2) := by
  calc
    uniformMean (fun a => variance (fun b => f (a, b))) =
        uniformMean (fun a =>
          uniformMean (fun b => (f (a, b)) ^ 2) -
            (uniformMean (fun b => f (a, b))) ^ 2) := by
          congr 1
          funext a
          exact variance_eq_mean_sq_sub_sqmean (fun b => f (a, b))
    _ = uniformMean (fun a => uniformMean (fun b => (f (a, b)) ^ 2)) -
          uniformMean (fun a => (uniformMean (fun b => f (a, b))) ^ 2) :=
        uniformMean_sub _ _
    _ = _ := by rw [← uniformMean_fubini (fun p : A × B => (f p) ^ 2)]

theorem S4_ES_02Statement_holds : ThLean.BP.S4.S4_ES_02Statement := by
  intro A B instA instB nonA nonB f
  let g : A → ℝ := fun a => uniformMean (fun b => f (a, b))
  constructor
  · have hmean : uniformMean f = uniformMean g := by
      simpa [g] using uniformMean_fubini f
    calc
      variance f = uniformMean (fun p : A × B => (f p) ^ 2) -
          (uniformMean f) ^ 2 := variance_eq_mean_sq_sub_sqmean f
      _ = (uniformMean (fun p : A × B => (f p) ^ 2) -
          uniformMean (fun a => (g a) ^ 2)) +
          (uniformMean (fun a => (g a) ^ 2) - (uniformMean g) ^ 2) := by
            rw [hmean]
            ring
      _ = uniformMean (fun a => variance (fun b => f (a, b))) + variance g := by
            rw [uniformMean_variance, variance_eq_mean_sq_sub_sqmean]
  · let d : (A × A) → B → ℝ := fun p b => f (p.1, b) - f (p.2, b)
    have hd (p : A × A) :
        uniformMean (d p) = g p.1 - g p.2 := by
      dsimp [d, g]
      rw [uniformMean_sub]
    have hj (p : A × A) :
        (g p.1 - g p.2) ^ 2 ≤ uniformMean (fun b => (d p b) ^ 2) := by
      rw [← hd p]
      exact uniformMean_sq_le (d p)
    calc
      variance g = (1 / 2 : ℝ) *
          uniformMean (fun p : A × A => (g p.1 - g p.2) ^ 2) :=
            variance_two_copy g
      _ ≤ (1 / 2 : ℝ) *
          uniformMean (fun p : A × A => uniformMean (fun b => (d p b) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left (uniformMean_mono hj) (by norm_num)
      _ = uniformMean (fun b => variance (fun a => f (a, b))) := by
            calc
              (1 / 2 : ℝ) *
                  uniformMean (fun p : A × A => uniformMean (fun b => (d p b) ^ 2)) =
                  (1 / 2 : ℝ) *
                    uniformMean (fun b => uniformMean (fun p : A × A => (d p b) ^ 2)) := by
                      congr 1
                      exact uniformMean_fubini_swap (A := A × A) (B := B)
                        (fun q : (A × A) × B => (d q.1 q.2) ^ 2)
              _ = uniformMean (fun b => variance (fun a => f (a, b))) := by
                have hpair (b : B) :
                    uniformMean (fun p : A × A => (d p b) ^ 2) =
                      2 * variance (fun a => f (a, b)) := by
                  dsimp [d]
                  have := variance_two_copy (fun a => f (a, b))
                  linarith
                simp_rw [hpair]
                rw [uniformMean_const_mul]
                ring

end ThLean.W.S403

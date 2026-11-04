module

public import ThLean.BP.S4.Finite

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ThLean.W.S406
open ThresholdFoundations

private lemma uniformMean_mono {A : Type} [Fintype A] [Nonempty A]
    (u v : A → ℝ) (h : ∀ x, u x ≤ v x) : uniformMean u ≤ uniformMean v := by
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›)
  unfold uniformMean
  rw [div_le_div_iff_of_pos_right hcard]
  exact Finset.sum_le_sum (fun x _ => h x)

private lemma uniformMean_mul_left {A : Type} [Fintype A] (c : ℝ) (u : A → ℝ) :
    uniformMean (fun x => c * u x) = c * uniformMean u := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

private lemma uniformMean_mul_right {A : Type} [Fintype A] (u : A → ℝ) (c : ℝ) :
    uniformMean (fun x => u x * c) = uniformMean u * c := by
  calc
    uniformMean (fun x => u x * c) = uniformMean (fun x => c * u x) := by
      congr 1
      funext x
      ring
    _ = c * uniformMean u := uniformMean_mul_left c u
    _ = uniformMean u * c := by ring

private lemma uniformMean_add {A : Type} [Fintype A] (u v : A → ℝ) :
    uniformMean (fun x => u x + v x) = uniformMean u + uniformMean v := by
  unfold uniformMean
  rw [Finset.sum_add_distrib]
  ring

private lemma uniformMean_product {A : Type} [Fintype A] [Nonempty A]
    (hfin : ThresholdFoundations.PreFiniteLawsStatement.{0,0}) (u v : A → ℝ) :
    uniformMean (fun z : A × A => u z.1 * v z.2) = uniformMean u * uniformMean v := by
  calc
    uniformMean (fun z : A × A => u z.1 * v z.2) =
        uniformMean (fun x => uniformMean (fun y => u x * v y)) :=
      hfin.2.1 A A (fun z : A × A => u z.1 * v z.2)
    _ = uniformMean (fun x => u x * uniformMean v) := by
      congr 1
      funext x
      rw [uniformMean_mul_left]
    _ = uniformMean u * uniformMean v := by
      rw [uniformMean_mul_right]

/-- Endpoint masses force a lower bound on variance, including for empty finite types. -/
theorem S4_RED_12Statement_of_deps
    (hES : ThLean.BP.S4.S4_ES_01Statement)
    (hfin : ThresholdFoundations.PreFiniteLawsStatement.{0,0}) :
    ThLean.BP.S4.S4_RED_12Statement := by
  classical
  intro A instA f a b hab
  by_cases hA : Nonempty A
  · letI : Nonempty A := hA
    let p : ℝ := uniformProb (fun x => f x = a)
    let q : ℝ := uniformProb (fun x => f x = b)
    let gap : ℝ := b - a
    have hAB : uniformMean (fun z : A × A =>
        indicator (f z.1 = a ∧ f z.2 = b)) = p * q := by
      calc
        uniformMean (fun z : A × A => indicator (f z.1 = a ∧ f z.2 = b)) =
            uniformMean (fun z : A × A =>
              indicator (f z.1 = a) * indicator (f z.2 = b)) := by
          congr 1
          funext z
          by_cases hx : f z.1 = a <;> by_cases hy : f z.2 = b <;>
            simp [ThresholdFoundations.indicator, hx, hy]
        _ = uniformMean (fun x => indicator (f x = a)) *
              uniformMean (fun y => indicator (f y = b)) :=
            uniformMean_product (A := A) hfin
              (fun x : A => indicator (f x = a))
              (fun y : A => indicator (f y = b))
        _ = p * q := rfl
    have hBA : uniformMean (fun z : A × A =>
        indicator (f z.1 = b ∧ f z.2 = a)) = q * p := by
      calc
        uniformMean (fun z : A × A => indicator (f z.1 = b ∧ f z.2 = a)) =
            uniformMean (fun z : A × A =>
              indicator (f z.1 = b) * indicator (f z.2 = a)) := by
          congr 1
          funext z
          by_cases hx : f z.1 = b <;> by_cases hy : f z.2 = a <;>
            simp [ThresholdFoundations.indicator, hx, hy]
        _ = uniformMean (fun x => indicator (f x = b)) *
              uniformMean (fun y => indicator (f y = a)) :=
            uniformMean_product (A := A) hfin
              (fun x : A => indicator (f x = b))
              (fun y : A => indicator (f y = a))
        _ = q * p := rfl
    have hpoint : ∀ z : A × A,
        indicator (f z.1 = a ∧ f z.2 = b) * gap ^ 2 +
          indicator (f z.1 = b ∧ f z.2 = a) * gap ^ 2 ≤
            (f z.1 - f z.2) ^ 2 := by
      intro z
      rcases lt_or_eq_of_le hab with hlt | heq
      · by_cases h₁ : f z.1 = a ∧ f z.2 = b
        · rcases h₁ with ⟨h₁a, h₁b⟩
          have h₂ : ¬ (f z.1 = b ∧ f z.2 = a) := by
            rintro ⟨h₂b, h₂a⟩
            exact hlt.ne (h₁a.symm.trans h₂b)
          simp [ThresholdFoundations.indicator, gap, h₁a, h₁b, hlt.ne]
          nlinarith
        · by_cases h₂ : f z.1 = b ∧ f z.2 = a
          · rcases h₂ with ⟨h₂b, h₂a⟩
            simp [ThresholdFoundations.indicator, gap, h₂b, h₂a, Ne.symm hlt.ne]
          · simp [ThresholdFoundations.indicator, gap, h₁, h₂]
            positivity
      · subst b
        simp [gap, ThresholdFoundations.indicator]
        positivity
    have hmean : uniformMean (fun z : A × A =>
        indicator (f z.1 = a ∧ f z.2 = b) * gap ^ 2 +
          indicator (f z.1 = b ∧ f z.2 = a) * gap ^ 2) ≤
        uniformMean (fun z : A × A => (f z.1 - f z.2) ^ 2) :=
      uniformMean_mono _ _ hpoint
    have hlow : (1 / 2 : ℝ) * uniformMean (fun z : A × A =>
        indicator (f z.1 = a ∧ f z.2 = b) * gap ^ 2 +
          indicator (f z.1 = b ∧ f z.2 = a) * gap ^ 2) = p * q * gap ^ 2 := by
      rw [uniformMean_add, uniformMean_mul_right, uniformMean_mul_right, hAB, hBA]
      dsimp [gap]
      ring
    have hvar : p * q * gap ^ 2 ≤ variance f := by
      calc
        p * q * gap ^ 2 = (1 / 2 : ℝ) * uniformMean (fun z : A × A =>
            indicator (f z.1 = a ∧ f z.2 = b) * gap ^ 2 +
              indicator (f z.1 = b ∧ f z.2 = a) * gap ^ 2) := hlow.symm
        _ ≤ (1 / 2 : ℝ) * uniformMean (fun z : A × A =>
            (f z.1 - f z.2) ^ 2) :=
          mul_le_mul_of_nonneg_left hmean (by norm_num)
        _ = variance f := (hES A f a).2.1.symm
    constructor
    · simpa [p, q, gap] using hvar
    · intro η hη hηa hηb
      have hηp : η * p ≤ p * q := by
        have hpη : η * η ≤ η * p := mul_le_mul_of_nonneg_left hηa hη
        have hqη : η * η ≤ η * q := mul_le_mul_of_nonneg_left hηb hη
        have hprod : 0 ≤ (p - η) * (q - η) :=
          mul_nonneg (sub_nonneg.mpr hηa) (sub_nonneg.mpr hηb)
        nlinarith [hpη, hqη, hprod]
      have hηsq : η ^ 2 ≤ p * q := by nlinarith [hηp]
      have hηvar : η ^ 2 * gap ^ 2 ≤ p * q * gap ^ 2 :=
        mul_le_mul_of_nonneg_right hηsq (sq_nonneg gap)
      exact hηvar.trans (by simpa using hvar)
  · letI : IsEmpty A := not_nonempty_iff.mp hA
    constructor
    · simp [uniformProb, uniformMean, variance]
    · intro η hη hηa hηb
      have hηzero : η = 0 := le_antisymm (by simpa [uniformProb, uniformMean] using hηa) hη
      subst η
      simp [uniformMean, variance]

end ThLean.W.S406

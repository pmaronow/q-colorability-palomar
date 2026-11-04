module

public import ThLean.BP.SA.Interpolation

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA27S
open ThresholdFoundations ThLean.BP.SA

variable {A B : Type}

lemma indicator_norm_le (P : Prop) : ‖indicator P‖ ≤ 1 := by
  simp only [indicator]
  split_ifs <;> norm_num

lemma summable_weighted {a : A → ℝ} (ha : Summable a)
    (F : A → ℝ) (hF : ∀ x, ‖F x‖ ≤ 1) :
    Summable (fun x => a x * F x) := by
  apply Summable.of_norm_bounded ha.norm
  intro x
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hF x) (norm_nonneg _)).trans_eq (mul_one _)

/-- Regroup a summable signed weight by a statistic, retaining bounded observables. -/
lemma tsum_pushforward {a : A → ℝ} (ha : Summable a) (g : A → B)
    (b : B → ℝ) (hg : ∀ y, (∑' x : {x // g x = y}, a x.val) = b y)
    (F : B → ℝ) (hF : ∀ y, ‖F y‖ ≤ 1) :
    (∑' x, a x * F (g x)) = ∑' y, b y * F y := by
  have hs := summable_weighted ha (fun x => F (g x)) (fun x => hF (g x))
  calc
    (∑' x, a x * F (g x)) =
        ∑' y, ∑' x : {x // g x = y}, a x.val * F (g x.val) :=
      (hs.hasSum.tsum_fiberwise g).tsum_eq.symm
    _ = ∑' y, b y * F y := by
      apply tsum_congr
      intro y
      simp_rw [show ∀ x : {x // g x = y}, g x.val = y from fun x => x.property]
      rw [tsum_mul_right, hg y]

lemma fiber_tsum_eq_indicator (a : A → ℝ) (g : A → B) (y : B) :
    (∑' x : {x // g x = y}, a x.val) = ∑' x, a x * indicator (g x = y) := by
  change (∑' x : ({x | g x = y} : Set A), a x.val) = _
  rw [tsum_subtype]
  apply tsum_congr
  intro x
  by_cases h : g x = y <;> simp [indicator, h]

abbrev Prefix (D : Type) := Σ k : ℕ, Fin k → D

def prefixWeight (D : Type) [Fintype D] (μ : ℝ) (p : Prefix D) : ℝ :=
  poissonWeight μ p.1 / (Fintype.card (Fin p.1 → D) : ℝ)

def histogram {D : Type} [DecidableEq D] (p : Prefix D) (d : D) : ℕ :=
  (List.ofFn p.2).count d

lemma poissonWeight_summable (μ : ℝ) : Summable (poissonWeight μ) := by
  have hs := (Real.summable_pow_div_factorial μ).mul_left (Real.exp (-μ))
  exact hs.congr (fun k => (mul_div_assoc _ _ _).symm)

lemma prefixWeight_summable (D : Type) [Fintype D] [Nonempty D] (μ : ℝ) :
    Summable (prefixWeight D μ) := by
  apply Summable.of_norm
  apply (summable_sigma_of_nonneg (fun p => norm_nonneg (prefixWeight D μ p))).2
  refine ⟨fun k => Summable.of_finite, ?_⟩
  have hc : (Fintype.card D : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card D ≠ 0)
  convert (poissonWeight_summable μ).norm using 1
  funext k
  simp [prefixWeight, tsum_fintype, norm_div, nsmul_eq_mul, hc, mul_div_cancel₀]

lemma prefixWeight_mean (D : Type) [Fintype D] [Nonempty D] (μ : ℝ)
    (F : Prefix D → ℝ) (hF : ∀ p, ‖F p‖ ≤ 1) :
    (∑' p, prefixWeight D μ p * F p) =
      ∑' k, poissonWeight μ k * uniformMean (fun x : Fin k → D => F ⟨k, x⟩) := by
  have hs := summable_weighted (prefixWeight_summable D μ) F hF
  rw [hs.tsum_sigma]
  apply tsum_congr
  intro k
  rw [tsum_fintype]
  change (∑ x : Fin k → D, (poissonWeight μ k /
    (Fintype.card (Fin k → D) : ℝ)) * F ⟨k, x⟩) = _
  rw [← Finset.mul_sum]
  unfold uniformMean
  ring

lemma prefixWeight_histogram (h11a : SA_I11aStatement)
    (D : Type) [Fintype D] [DecidableEq D] [Nonempty D]
    (μ : ℝ) (z : D → ℕ) :
    (∑' p : {p : Prefix D // histogram p = z}, prefixWeight D μ p.val) =
      ∏ d, poissonWeight (μ / (Fintype.card D : ℝ)) (z d) := by
  have hc : (Fintype.card D : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card D ≠ 0)
  have hν : ∀ _d : D, 0 ≤ (1 / (Fintype.card D : ℝ)) := fun _ => by positivity
  have hsum : (∑ _d : D, (1 / (Fintype.card D : ℝ))) = 1 := by simp [hc]
  rw [fiber_tsum_eq_indicator, prefixWeight_mean D μ _ (fun _ => indicator_norm_le _)]
  convert h11a D (fun _ => 1 / (Fintype.card D : ℝ)) μ hν hsum z using 1
  · unfold weightedListMean poissonMixture
    apply tsum_congr
    intro k
    congr 1
    simp only [uniformMean, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fun, Nat.cast_pow, one_div_pow]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [div_eq_mul_inv, one_div, mul_comm]
    congr 1
    congr 1
    exact propext funext_iff
  · apply Finset.prod_congr rfl
    intro d _
    rw [div_eq_mul_one_div]

end ThLean.W.SA27S

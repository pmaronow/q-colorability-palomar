module

public import ThLean.W.SA40S.FiniteSampling

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ThLean.W.SA40S
open ThresholdFoundations

theorem uniform_probability_bounds {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProb P ∧ uniformProb P ≤ 1 := by
  have hsum : (∑ a, indicator (P a)) = ((Finset.univ.filter P).card : ℝ) := by
    simp only [indicator]
    exact Finset.sum_boole (R := ℝ) P Finset.univ
  rw [uniformProb, uniformMean, hsum]
  constructor
  · positivity
  · by_cases h : Fintype.card A = 0
    · simp [h]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h :
          (0 : ℝ) < Fintype.card A)).mpr
      exact_mod_cast Finset.card_filter_le (Finset.univ : Finset A) P

theorem process_survival_bounds {V : Type*} [Fintype V] (q m : ℕ) :
    0 ≤ processSurvival (V := V) q m ∧ processSurvival (V := V) q m ≤ 1 := by
  exact uniform_probability_bounds _

theorem poisson_weight_summable (z : ℝ) : Summable (poissonWeight z) := by
  have hs := (Real.summable_pow_div_factorial z).mul_left (Real.exp (-z))
  exact hs.congr (fun k => by simp [poissonWeight, div_eq_mul_inv, mul_assoc])

theorem poisson_weight_sum_one (z : ℝ) : (∑' k, poissonWeight z k) = 1 := by
  calc
    (∑' k, poissonWeight z k) = Real.exp (-z) * Real.exp z := by
      simpa [poissonWeight, mul_div_assoc, Real.exp_eq_exp_ℝ] using
        ((NormedSpace.expSeries_div_hasSum_exp z).mul_left (Real.exp (-z))).tsum_eq
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem poisson_mixture_bounds (z : ℝ) (hz : 0 ≤ z) (a : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k ∧ a k ≤ 1) :
    Summable (fun k => poissonWeight z k * a k) ∧
      0 ≤ poissonMixture z a ∧ poissonMixture z a ≤ 1 := by
  have hw (k : ℕ) : 0 ≤ poissonWeight z k := by
    unfold poissonWeight
    positivity
  have hnonneg (k : ℕ) : 0 ≤ poissonWeight z k * a k := mul_nonneg (hw k) (ha k).1
  have hle (k : ℕ) : poissonWeight z k * a k ≤ poissonWeight z k := by
    simpa using mul_le_mul_of_nonneg_left (ha k).2 (hw k)
  have hs := (poisson_weight_summable z).of_nonneg_of_le hnonneg hle
  refine ⟨hs, tsum_nonneg hnonneg, ?_⟩
  rw [poissonMixture, ← poisson_weight_sum_one z]
  exact hs.tsum_le_tsum hle (poisson_weight_summable z)

theorem loop_split_weight (n m : ℕ) (hn : 0 < n) (c : ℝ) :
    poissonWeight (c * n) m * (((n : ℝ) - 1) / n) ^ m =
      Real.exp (-c) * poissonWeight (c * ((n : ℝ) - 1)) m := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hrate : (c * n) * (((n : ℝ) - 1) / n) = c * ((n : ℝ) - 1) := by
    field_simp
  have hexp : Real.exp (-(c * n)) =
      Real.exp (-c) * Real.exp (-(c * ((n : ℝ) - 1))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow : (c * (n : ℝ)) ^ m * (((n : ℝ) - 1) / n) ^ m =
      (c * ((n : ℝ) - 1)) ^ m := by rw [← mul_pow, hrate]
  simp only [poissonWeight]
  rw [hexp]
  calc
    _ = (Real.exp (-c) * Real.exp (-(c * ((n : ℝ) - 1)))) *
        ((c * (n : ℝ)) ^ m * (((n : ℝ) - 1) / n) ^ m) / (m.factorial : ℝ) := by ring
    _ = _ := by rw [hpow]; ring

theorem rho_loop_split (q n : ℕ) (hn : 2 ≤ n) (c : ℝ) :
    rho q n c = Real.exp (-c) *
      poissonMixture (c * ((n : ℝ) - 1)) (processSurvival (V := Fin n) q) := by
  unfold rho poissonMixture
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  dsimp only
  rw [ordered_colorable_probability q n m hn, ← mul_assoc,
    loop_split_weight n m (by omega) c]
  ring

theorem SA_Q20Statement_holds : ThLean.BP.SA.SA_Q20Statement := by
  intro q n _ hn c hc
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hz : 0 ≤ c * ((n : ℝ) - 1) := mul_nonneg hc (sub_nonneg.mpr hn1)
  obtain ⟨hs, hnonneg, hle⟩ := poisson_mixture_bounds (c * ((n : ℝ) - 1)) hz
    (processSurvival (V := Fin n) q) (process_survival_bounds q)
  exact ⟨hs, hnonneg, hle, rho_loop_split q n hn c⟩

example : ThLean.BP.SA.SA_Q20Statement := SA_Q20Statement_holds

end ThLean.W.SA40S

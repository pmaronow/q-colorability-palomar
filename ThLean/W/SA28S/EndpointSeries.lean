import ThLean.W.SA28S.Coefficients

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA28S
open ThresholdFoundations ThLean.BP.SA

theorem poissonWeight_at_zero (m : ℕ) :
    poissonWeight 0 m = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0 <;> simp [poissonWeight, hm]

theorem chiBar_global (q n₁ n₂ : ℕ) (c : ℝ) :
    chiBar q n₁ n₂ (interpolationMeans n₁ n₂ c c) = rho q (n₁+n₂) c := by
  let e : ℕ → (Fin 3 → ℕ) := fun m => ![m, 0, 0]
  have he : Function.Injective e := by
    intro a b hab
    exact congrFun hab 0
  have hs : Function.support (fun k : Fin 3 → ℕ =>
      (∏ i : Fin 3, poissonWeight (interpolationMeans n₁ n₂ c c i) (k i)) *
        interpolationCoefficient q n₁ n₂ k) ⊆ Set.range e := by
    intro k hk
    have h₁ : k 1 = 0 := by
      by_contra h
      exact hk (by simp [Fin.prod_univ_three, interpolationMeans, poissonWeight_at_zero, h])
    have h₂ : k 2 = 0 := by
      by_contra h
      exact hk (by simp [Fin.prod_univ_three, interpolationMeans, poissonWeight_at_zero, h])
    refine ⟨k 0, ?_⟩
    ext i
    fin_cases i <;> simp [e, h₁, h₂]
  unfold chiBar
  rw [← he.tsum_eq hs]
  unfold rho poissonMixture
  apply tsum_congr
  intro m
  simp [e, Fin.prod_univ_three, interpolationMeans, poissonWeight_at_zero,
    coefficient_global, mul_comm]

theorem uniformProb_abs_le_one {A : Type} [Fintype A] [Nonempty A] (P : A → Prop) :
    |uniformProb P| ≤ 1 := by
  have hc : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have h₀ : 0 ≤ uniformProb P := by
    unfold uniformProb uniformMean
    apply div_nonneg _ hc.le
    exact Finset.sum_nonneg (fun a _ => by by_cases h : P a <;> simp [indicator, h])
  rw [abs_of_nonneg h₀]
  unfold uniformProb uniformMean
  apply (div_le_iff₀ hc).mpr
  calc
    (∑ a, indicator (P a)) ≤ ∑ _a : A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases h : P a <;> simp [indicator, h]
    _ = 1 * (Fintype.card A : ℝ) := by simp

theorem rho_series_norm_summable (q n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    Summable (fun m : ℕ => ‖poissonWeight (c * n) m *
      uniformProb (fun x : Fin m → Fin n × Fin n => Colorable q (orderedTupleGraph x))‖) := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hw : Summable (poissonWeight (c * n)) := by
    exact ((Real.summable_pow_div_factorial (c * n)).mul_left (Real.exp (-(c * n)))).congr
      (fun m => by simp only [poissonWeight, mul_div_assoc])
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hw.norm
  intro m
  rw [norm_mul]
  calc
    _ ≤ ‖poissonWeight (c * n) m‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Real.norm_eq_abs] using uniformProb_abs_le_one
        (fun x : Fin m → Fin n × Fin n => Colorable q (orderedTupleGraph x))
    _ = _ := mul_one _

theorem chiBar_local (q n₁ n₂ : ℕ) (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) (c : ℝ) :
    chiBar q n₁ n₂ (interpolationMeans n₁ n₂ c 0) = rho q n₁ c * rho q n₂ c := by
  let e : ℕ × ℕ → (Fin 3 → ℕ) := fun m => ![0, m.1, m.2]
  have he : Function.Injective e := by
    intro a b hab
    apply Prod.ext
    · exact congrFun hab 1
    · exact congrFun hab 2
  have hs : Function.support (fun k : Fin 3 → ℕ =>
      (∏ i : Fin 3, poissonWeight (interpolationMeans n₁ n₂ c 0 i) (k i)) *
        interpolationCoefficient q n₁ n₂ k) ⊆ Set.range e := by
    intro k hk
    have h₀ : k 0 = 0 := by
      by_contra h
      exact hk (by simp [Fin.prod_univ_three, interpolationMeans, poissonWeight_at_zero, h])
    refine ⟨(k 1, k 2), ?_⟩
    ext i
    fin_cases i <;> simp [e, h₀]
  unfold chiBar
  rw [← he.tsum_eq hs]
  unfold rho poissonMixture
  rw [tsum_mul_tsum_of_summable_norm (rho_series_norm_summable q n₁ h₁ c)
    (rho_series_norm_summable q n₂ h₂ c)]
  apply tsum_congr
  intro m
  simp only [e, Fin.prod_univ_three, interpolationMeans]
  simp [poissonWeight_at_zero, coefficient_local, mul_comm, mul_left_comm, mul_assoc]

end ThLean.W.SA28S

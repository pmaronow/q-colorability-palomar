import ThLean.W.SA27S.TripleWeights

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA27S
open ThresholdFoundations ThLean.BP.SA

private lemma sum_three_uniform (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    (a b c : ℝ) (F : A → B → C → ℝ) :
    (∑ x : A, ∑ y : B, ∑ z : C,
      (a / (Fintype.card A : ℝ)) *
        ((b / (Fintype.card B : ℝ)) * (c / (Fintype.card C : ℝ))) * F x y z) =
      (a * (b * c)) * uniformMean (fun x =>
        uniformMean (fun y => uniformMean (fun z => F x y z))) := by
  unfold uniformMean
  simp_rw [Finset.sum_div, ← mul_div_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

def threeCountsEquiv : (Fin 3 → ℕ) ≃ ℕ × (ℕ × ℕ) where
  toFun k := (k 0, k 1, k 2)
  invFun k := ![k.1, k.2.1, k.2.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv k := rfl

def prefixTripleEquiv (A B C : Type) : TriplePrefix A B C ≃
    Σ k : ℕ × (ℕ × ℕ), (Fin k.1 → A) × ((Fin k.2.1 → B) × (Fin k.2.2 → C)) where
  toFun p := ⟨(p.1.1, p.2.1.1, p.2.2.1), (p.1.2, p.2.1.2, p.2.2.2)⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2.1, p.2.2.1⟩, ⟨p.1.2.2, p.2.2.2⟩)
  left_inv p := by rcases p with ⟨⟨k₀, x₀⟩, ⟨k₁, x₁⟩, ⟨k₂, x₂⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨k₀, k₁, k₂⟩, x₀, x₁, x₂⟩; rfl

/-- The three-family factorial series is the sum over independent endpoint prefixes. -/
lemma triplePrefix_mean (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (μ : Fin 3 → ℝ) (F : TriplePrefix A B C → ℝ) (hF : ∀ p, ‖F p‖ ≤ 1) :
    (∑' p : TriplePrefix A B C,
      tripleWeight (prefixWeight A (μ 0)) (prefixWeight B (μ 1))
        (prefixWeight C (μ 2)) p * F p) =
    ∑' k : Fin 3 → ℕ, (∏ i, poissonWeight (μ i) (k i)) *
      uniformMean (fun x₀ : Fin (k 0) → A =>
        uniformMean (fun x₁ : Fin (k 1) → B =>
          uniformMean (fun x₂ : Fin (k 2) → C =>
            F (⟨k 0, x₀⟩, ⟨k 1, x₁⟩, ⟨k 2, x₂⟩)))) := by
  let term : TriplePrefix A B C → ℝ := fun p =>
    tripleWeight (prefixWeight A (μ 0)) (prefixWeight B (μ 1))
      (prefixWeight C (μ 2)) p * F p
  have hs : Summable term := summable_weighted
    (tripleWeight_summable (prefixWeight_summable A (μ 0))
      (prefixWeight_summable B (μ 1)) (prefixWeight_summable C (μ 2))) F hF
  let e := prefixTripleEquiv A B C
  have hs' : Summable (fun p => term (e.symm p)) := (e.symm.summable_iff).mpr hs
  calc
    (∑' p, term p) = ∑' p, term (e.symm p) := (e.symm.tsum_eq term).symm
    _ = ∑' k : ℕ × (ℕ × ℕ),
        (poissonWeight (μ 0) k.1 * (poissonWeight (μ 1) k.2.1 *
          poissonWeight (μ 2) k.2.2)) *
        uniformMean (fun x₀ : Fin k.1 → A =>
          uniformMean (fun x₁ : Fin k.2.1 → B =>
            uniformMean (fun x₂ : Fin k.2.2 → C =>
              F (⟨k.1, x₀⟩, ⟨k.2.1, x₁⟩, ⟨k.2.2, x₂⟩)))) := by
      rw [hs'.tsum_sigma]
      apply tsum_congr
      intro k
      simp only [tsum_fintype, Fintype.sum_prod_type]
      exact sum_three_uniform _ _ _ (poissonWeight (μ 0) k.1)
        (poissonWeight (μ 1) k.2.1) (poissonWeight (μ 2) k.2.2)
        (fun x₀ x₁ x₂ => F (⟨k.1, x₀⟩, ⟨k.2.1, x₁⟩, ⟨k.2.2, x₂⟩))
    _ = _ := by
      rw [← threeCountsEquiv.tsum_eq]
      apply tsum_congr
      intro k
      simp only [threeCountsEquiv, Fin.prod_univ_three, mul_assoc]
      rfl

end ThLean.W.SA27S

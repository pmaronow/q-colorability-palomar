module

public import ThLean.W.SA28S.Graph

@[expose] public section

/-!
The finite-average helpers `mean_const`
match implementation patterns in OpenAI's math library (Apache-2.0).
Local versions use project-specific averaging definitions and namespaces.
Their source credits and licence scope are listed in NOTICE; the licence
text is in LICENSES/Apache-2.0.txt.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA28S
open ThresholdFoundations

theorem orderedTupleGraph_empty {V : Type} [Fintype V] (x : Fin 0 → V × V) :
    orderedTupleGraph x = 0 := by
  ext e
  simp [orderedTupleGraph]

theorem mean_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  simp [uniformMean, Fintype.card_ne_zero]

theorem mean_mul_const {A : Type} [Fintype A] (f : A → ℝ) (c : ℝ) :
    uniformMean (fun a => f a * c) = uniformMean f * c := by
  simp [uniformMean, Finset.sum_mul, div_mul_eq_mul_div]

theorem mean_const_mul {A : Type} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

theorem indicator_and (P Q : Prop) : indicator (P ∧ Q) = indicator P * indicator Q := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [indicator, hP, hQ]

theorem coefficient_local (q n₁ n₂ m₁ m₂ : ℕ) :
    interpolationCoefficient q n₁ n₂ ![0, m₁, m₂] =
      uniformProb (fun x : Fin m₁ → Fin n₁ × Fin n₁ => Colorable q (orderedTupleGraph x)) *
      uniformProb (fun x : Fin m₂ → Fin n₂ × Fin n₂ => Colorable q (orderedTupleGraph x)) := by
  change uniformMean (fun x₀ : Fin 0 → Fin (n₁+n₂) × Fin (n₁+n₂) =>
    uniformMean (fun x₁ : Fin m₁ → Fin n₁ × Fin n₁ =>
      uniformMean (fun x₂ : Fin m₂ → Fin n₂ × Fin n₂ =>
        indicator (Colorable q (mixedGraph x₀ x₁ x₂))))) = _
  simp_rw [mixedGraph, orderedTupleGraph_empty, zero_add, colorable_blocks_iff, indicator_and,
    mean_const_mul, mean_mul_const, mean_const]
  rfl

theorem coefficient_global (q n₁ n₂ m : ℕ) :
    interpolationCoefficient q n₁ n₂ ![m, 0, 0] =
      uniformProb (fun x : Fin m → Fin (n₁ + n₂) × Fin (n₁ + n₂) =>
        Colorable q (orderedTupleGraph x)) := by
  change uniformMean (fun x₀ : Fin m → Fin (n₁+n₂) × Fin (n₁+n₂) =>
    uniformMean (fun x₁ : Fin 0 → Fin n₁ × Fin n₁ =>
      uniformMean (fun x₂ : Fin 0 → Fin n₂ × Fin n₂ =>
        indicator (Colorable q (mixedGraph x₀ x₁ x₂))))) = _
  have hm (f : Fin n₁ → Fin (n₁ + n₂)) : mapGraph f (0 : MGraph (Fin n₁)) = 0 := by
    ext e
    simp [mapGraph]
  have hm' (f : Fin n₂ → Fin (n₁ + n₂)) : mapGraph f (0 : MGraph (Fin n₂)) = 0 := by
    ext e
    simp [mapGraph]
  simp_rw [mixedGraph, orderedTupleGraph_empty, hm, hm', add_zero, mean_const]
  rfl

end ThLean.W.SA28S

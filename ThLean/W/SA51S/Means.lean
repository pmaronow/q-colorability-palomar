import ThLean.BP.SA.Alternatives

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA51S
open ThresholdFoundations ThLean.BP.SA

lemma mean_add {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

lemma mean_mul {A : Type} [Fintype A] (r : ℝ) (f : A → ℝ) :
    uniformMean (fun a => r * f a) = r * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_mul_right {A : Type} [Fintype A] (r : ℝ) (f : A → ℝ) :
    uniformMean (fun a => f a * r) = uniformMean f * r := by
  simpa only [mul_comm] using mean_mul r f

lemma mean_congr {A : Type} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a = g a) :
    uniformMean f = uniformMean g := by rw [show f = g from funext h]

lemma mean_comm {A B : Type} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  simp only [uniformMean, ← Finset.sum_div, div_div]
  rw [Finset.sum_comm, mul_comm]

lemma mean_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a => f (e a)) = uniformMean f := by
  simp only [uniformMean, Fintype.card_congr e, Equiv.sum_comp]

lemma mean_cons {A : Type} [Fintype A] (m : ℕ) (f : (Fin (m+1) → A) → ℝ) :
    uniformMean f = uniformMean (fun a =>
      uniformMean (fun x : Fin m → A => f (Fin.cons a x))) := by
  rw [← mean_equiv (Fin.consEquiv (fun _ : Fin (m+1) => A)) f]
  simp [uniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, div_div, Fin.consEquiv, mul_comm]

lemma mean_bounds {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 := by
  have hc : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun a _ => (hf a).1) hc.le
  · apply (div_le_iff₀ hc).2
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => (hf a).2)

/-- A finite average of deterministic transitions, viewed as a linear operator. -/
def averageOp {X A : Type} [Fintype A] (move : X → A → X) :
    Module.End ℝ (X → ℝ) where
  toFun f x := uniformMean (fun a => f (move x a))
  map_add' f g := funext fun x => mean_add _ _
  map_smul' r f := funext fun x => mean_mul r _

lemma averageOp_pow_bounds {X A : Type} [Fintype A] [Nonempty A]
    (move : X → A → X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (m : ℕ) (x : X) :
    0 ≤ (averageOp move ^ m) f x ∧ (averageOp move ^ m) f x ≤ 1 := by
  induction m generalizing x with
  | zero => exact hf x
  | succ m ih =>
    rw [pow_succ']
    exact mean_bounds _ (fun a => ih (move x a))

lemma indicator_bounds (P : Prop) : 0 ≤ indicator P ∧ indicator P ≤ 1 := by
  by_cases h : P <;> simp [indicator, h]

end ThLean.W.SA51S

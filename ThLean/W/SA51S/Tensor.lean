import ThLean.W.SA51S.Means

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA51S
open ThresholdFoundations

variable {X Y A B : Type} [Fintype A] [Fintype B]

def leftOp (move : X → A → X) : Module.End ℝ (X × Y → ℝ) :=
  averageOp (fun z a => (move z.1 a, z.2))

def rightOp (move : Y → B → Y) : Module.End ℝ (X × Y → ℝ) :=
  averageOp (fun z b => (z.1, move z.2 b))

lemma left_right_commute (u : X → A → X) (v : Y → B → Y) :
    Commute (leftOp (Y := Y) u) (rightOp (X := X) v) := by
  ext f z
  change uniformMean (fun a => uniformMean (fun b => f (u z.1 a, v z.2 b))) =
    uniformMean (fun b => uniformMean (fun a => f (u z.1 a, v z.2 b)))
  exact mean_comm _

lemma left_pow_product (u : X → A → X) (f : X → ℝ) (g : Y → ℝ)
    (m : ℕ) (x : X) (y : Y) :
    (leftOp u ^ m) (fun z => f z.1 * g z.2) (x,y) =
      (averageOp u ^ m) f x * g y := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ']
    change uniformMean (fun a => (leftOp u ^ m) (fun z => f z.1 * g z.2) (u x a,y)) =
      uniformMean (fun a => (averageOp u ^ m) f (u x a)) * g y
    simp_rw [ih]
    exact mean_mul_right _ _

lemma right_pow_product (v : Y → B → Y) (f : X → ℝ) (g : Y → ℝ)
    (m : ℕ) (x : X) (y : Y) :
    (rightOp v ^ m) (fun z => f z.1 * g z.2) (x,y) =
      f x * (averageOp v ^ m) g y := by
  induction m generalizing y with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ']
    change uniformMean (fun b => (rightOp v ^ m) (fun z => f z.1 * g z.2) (x,v y b)) =
      f x * uniformMean (fun b => (averageOp v ^ m) g (v y b))
    simp_rw [ih]
    exact mean_mul _ _

lemma mixed_pow_product (u : X → A → X) (v : Y → B → Y)
    (f : X → ℝ) (g : Y → ℝ) (i j : ℕ) (x : X) (y : Y) :
    ((leftOp (Y := Y) u ^ i) * (rightOp (X := X) v ^ j))
      (fun z => f z.1 * g z.2) (x,y) =
      (averageOp u ^ i) f x * (averageOp v ^ j) g y := by
  have h : (rightOp v ^ j) (fun z : X × Y => f z.1 * g z.2) =
      fun z => f z.1 * (averageOp v ^ j) g z.2 := by
    funext z
    exact right_pow_product v f g j z.1 z.2
  change (leftOp u ^ i) ((rightOp v ^ j) (fun z => f z.1 * g z.2)) (x,y) = _
  rw [h]
  exact left_pow_product _ _ _ _ _ _

/-- The binomial expansion of independent moves in the two coordinates. -/
lemma tensor_binomial (u : X → A → X) (v : Y → B → Y)
    (f : X → ℝ) (g : Y → ℝ) (a b : ℝ) (m : ℕ) (x : X) (y : Y) :
    ((a • leftOp (Y := Y) u + b • rightOp (X := X) v) ^ m)
      (fun z => f z.1 * g z.2) (x,y) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
        (m.choose ij.1 : ℝ) * a ^ ij.1 * b ^ ij.2 *
          ((averageOp u ^ ij.1) f x * (averageOp v ^ ij.2) g y) := by
  have h : Commute (a • leftOp (Y := Y) u) (b • rightOp (X := X) v) := by
    ext f z
    change a * uniformMean (fun i => b * uniformMean (fun j => f (u z.1 i,v z.2 j))) =
      b * uniformMean (fun j => a * uniformMean (fun i => f (u z.1 i,v z.2 j)))
    rw [mean_mul, mean_mul, mean_comm]
    ring
  rw [h.add_pow']
  simp only [LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [smul_pow, smul_pow, smul_mul_smul_comm]
  rw [nsmul_eq_mul, Module.End.mul_apply, Module.End.natCast_apply]
  simp only [Pi.smul_apply, LinearMap.smul_apply, nsmul_eq_mul,
    smul_eq_mul, mixed_pow_product]
  ring

end ThLean.W.SA51S

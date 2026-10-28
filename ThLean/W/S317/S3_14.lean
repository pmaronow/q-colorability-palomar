import ThLean.BP.S3.Terminal

noncomputable section
open scoped BigOperators ENNReal
namespace ThLean.W.S317
open ThresholdFoundations ThLean.BP.S3

private theorem uniformMeanENN_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → ℝ≥0∞) :
    uniformMeanENN (fun p : A × B => f p.1 p.2) =
      uniformMeanENN (fun a : A => uniformMeanENN (f a)) := by
  classical
  simp only [uniformMeanENN, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul Finset.univ (fun a => ∑ b, f a b)
    ((Fintype.card B : ℝ≥0∞)⁻¹)]
  rw [ENNReal.mul_inv (by right; exact ENNReal.natCast_ne_top _)
    (by left; exact ENNReal.natCast_ne_top _)]
  simp only [mul_assoc, mul_comm, mul_left_comm]

private theorem uniformMean_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → ℝ) :
    uniformMean (fun p : A × B => f p.1 p.2) =
      uniformMean (fun a : A => uniformMean (f a)) := by
  classical
  simp only [uniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.sum_div Finset.univ (fun a => ∑ b, f a b) (Fintype.card B : ℝ)]
  simp only [div_div, mul_comm]

private theorem uniformMeanENN_mul_left {B : Type*} [Fintype B]
    (c : ℝ≥0∞) (f : B → ℝ≥0∞) :
    uniformMeanENN (fun b => c * f b) = c * uniformMeanENN f := by
  classical
  unfold uniformMeanENN
  calc
    (∑ b, c * f b) / (Fintype.card B : ℝ≥0∞) =
        (c * ∑ b, f b) / (Fintype.card B : ℝ≥0∞) := by
          congr 1
          exact (Finset.mul_sum Finset.univ f c).symm
    _ = c * ((∑ b, f b) / (Fintype.card B : ℝ≥0∞)) := by
          rw [mul_div_assoc]

private theorem uniformMean_mul_left {B : Type*} [Fintype B]
    (c : ℝ) (f : B → ℝ) :
    uniformMean (fun b => c * f b) = c * uniformMean f := by
  classical
  unfold uniformMean
  calc
    (∑ b, c * f b) / (Fintype.card B : ℝ) =
        (c * ∑ b, f b) / (Fintype.card B : ℝ) := by
          congr 1
          exact (Finset.mul_sum Finset.univ f c).symm
    _ = c * ((∑ b, f b) / (Fintype.card B : ℝ)) := by rw [mul_div_assoc]

private theorem uniformMeanENN_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ≥0∞) :
    uniformMeanENN (fun a : A => f (e a)) = uniformMeanENN f := by
  classical
  simp [uniformMeanENN, Equiv.sum_comp, Fintype.card_congr e]

private theorem uniformMean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a : A => f (e a)) = uniformMean f := by
  classical
  simp [uniformMean, Equiv.sum_comp, Fintype.card_congr e]

private def edgeTupleSnocEquiv (V : Type*) [Fintype V] (m : ℕ) :
    EdgeTuple V m × Pair V ≃ EdgeTuple V (m + 1) :=
  (Equiv.prodComm (EdgeTuple V m) (Pair V)).trans
    (Fin.snocEquiv (fun _ : Fin (m + 1) => Pair V))

private theorem edgeTupleSnocEquiv_init (V : Type*) [Fintype V] (m : ℕ)
    (p : EdgeTuple V m × Pair V) :
    initTuple (edgeTupleSnocEquiv V m p) = p.1 := by
  funext i
  simp [edgeTupleSnocEquiv, initTuple, Fin.snocEquiv]

private theorem edgeTupleSnocEquiv_last (V : Type*) [Fintype V] (m : ℕ)
    (p : EdgeTuple V m × Pair V) :
    lastPair (edgeTupleSnocEquiv V m p) = p.2 := by
  simp [edgeTupleSnocEquiv, lastPair, Fin.snocEquiv]

theorem S3_14Statement_holds : ThLean.BP.S3.S3_14Statement := by
  classical
  intro V _ hV m
  constructor
  · intro z F
    calc
      uniformMeanENN (fun x : EdgeTuple V (m+1) =>
          z (initTuple x) * F (initTuple x) (lastPair x))
          = uniformMeanENN (fun p : EdgeTuple V m × Pair V =>
              z p.1 * F p.1 p.2) := by
                symm
                simpa [edgeTupleSnocEquiv_init, edgeTupleSnocEquiv_last] using
                  uniformMeanENN_equiv (edgeTupleSnocEquiv V m)
                    (fun x => z (initTuple x) * F (initTuple x) (lastPair x))
      _ = uniformMeanENN (fun x : EdgeTuple V m =>
            z x * uniformMeanENN (F x)) := by
              exact (uniformMeanENN_prod (A := EdgeTuple V m) (B := Pair V)
                (fun x e => z x * F x e)).trans (by
                  congr 1
                  funext x
                  exact uniformMeanENN_mul_left (z x) (F x))
  · intro z F
    calc
      uniformMean (fun x : EdgeTuple V (m+1) =>
          z (initTuple x) * F (initTuple x) (lastPair x))
          = uniformMean (fun p : EdgeTuple V m × Pair V =>
              z p.1 * F p.1 p.2) := by
                symm
                simpa [edgeTupleSnocEquiv_init, edgeTupleSnocEquiv_last] using
                  uniformMean_equiv (edgeTupleSnocEquiv V m)
                    (fun x => z (initTuple x) * F (initTuple x) (lastPair x))
      _ = uniformMean (fun x : EdgeTuple V m =>
            z x * uniformMean (F x)) := by
              exact (uniformMean_prod (A := EdgeTuple V m) (B := Pair V)
                (fun x e => z x * F x e)).trans (by
                  congr 1
                  funext x
                  exact uniformMean_mul_left (z x) (F x))

end ThLean.W.S317

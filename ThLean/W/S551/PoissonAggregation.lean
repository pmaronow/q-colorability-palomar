import ThLean.Contrib.S551.PoissonAggregation

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S551

open ThresholdFoundations

private def cellFunEquiv (V : Type) (D j : ℕ) :
    (Fin j → Fin D × V) ≃ ((Fin j → Fin D) × (Fin j → V)) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv x := by funext i; simp
  right_inv p := by cases p; simp

private lemma cellProjection_uniformMean (V : Type) [Fintype V] (D j : ℕ)
    (hD : 0 < D) (g : (Fin j → V) → ℝ) :
    uniformMean (fun x : Fin j → Fin D × V => g (fun i => (x i).2)) = uniformMean g := by
  let e := cellFunEquiv V D j
  let A := Fin j → Fin D
  let B := Fin j → V
  have hA : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, by omega⟩⟩
  have hsum : (∑ x : Fin j → Fin D × V, g (fun i => (x i).2)) =
      ∑ p : A × B, g p.2 := by
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  unfold uniformMean
  rw [hsum, Fintype.card_congr e, Fintype.card_prod, Fintype.sum_prod_type]
  have hs : (∑ a : A, ∑ b : B, g b) =
      (Fintype.card A : ℝ) * ∑ b : B, g b := by simp
  rw [hs]
  push_cast
  have hAr : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hA
  field_simp [ne_of_gt hAr] <;> ring

private lemma poissonMixture_zero_congr (a b : ℕ → ℝ) (h0 : a 0 = b 0) :
    poissonMixture 0 a = poissonMixture 0 b := by
  unfold poissonMixture
  apply tsum_congr
  intro j
  cases j with
  | zero => simp [poissonWeight, h0]
  | succ j => simp [poissonWeight]

/-- The S5.09C identity follows from count-table Poissonization and a finite label projection. -/
theorem S5_09CStatement_from_gaps
    (h08A : ThLean.BP.S5.S5_08AStatement)
    (hE06B : ThLean.BP.S5.S5_E06BStatement)
    (hE08 : ThLean.BP.S5.S5_E08Statement)
    (hCells : ThLean.Contrib.S551.CellPoissonizationStatement) :
    ThLean.BP.S5.S5_09CStatement := by
  intro V instV instNonempty D r hr f hf
  calc
    _ = poissonMixture (D * Fintype.card V * r) (fun j =>
          uniformMean (fun x : Fin j → Fin D × V =>
            f (fun v => (Finset.univ.filter (fun i => (x i).2 = v)).card))) :=
      hCells h08A hE06B hE08 V D r hr f hf
    _ = poissonMixture (D * Fintype.card V * r) (fun j =>
          uniformMean (fun x : Fin j → V =>
            f (fun v => (Finset.univ.filter (fun i => x i = v)).card))) := by
      by_cases hD : D = 0
      · subst D
        simp only [Nat.cast_zero, zero_mul]
        apply poissonMixture_zero_congr
        simp [uniformMean]
      · have hDpos : 0 < D := Nat.pos_of_ne_zero hD
        unfold poissonMixture
        apply tsum_congr
        intro j
        exact congrArg (fun z : ℝ => poissonWeight (D * Fintype.card V * r) j * z)
          (cellProjection_uniformMean V D j hDpos
            (fun x => f (fun v => (Finset.univ.filter (fun i => x i = v)).card)))

end ThLean.W.S551

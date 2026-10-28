import ThLean.W.S551S.Series

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S551S

open ThresholdFoundations

private def cellFunEquiv (V : Type) (D j : ℕ) :
    (Fin j → Fin D × V) ≃ ((Fin j → Fin D) × (Fin j → V)) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv x := by funext i; simp
  right_inv p := by cases p; simp

/-- Forgetting the first coordinate of uniform cell labels preserves uniform means.
This is the finite projection from the earlier S551 attempt. -/
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
  field_simp [ne_of_gt hAr]
  ring

private lemma histogram_projection {V : Type} [Fintype V] (D m : ℕ)
    (x : Fin m → Fin D × V) (v : V) :
    (∑ a : Fin D, histogram x (a, v)) =
      histogram (fun i => (x i).2) v := by
  classical
  simp only [histogram, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hv : (x i).2 = v <;> simp [Prod.ext_iff, hv, eq_comm]

private lemma poissonMixture_at_zero (a : ℕ → ℝ) : poissonMixture 0 a = a 0 := by
  unfold poissonMixture
  rw [tsum_eq_single 0]
  · simp [poissonWeight]
  · intro j hj
    simp [poissonWeight, zero_pow hj]

/-- Crossing counts aggregate to one Poisson uniform list. Only the histogram
point-probability leaf is needed as a premise. -/
theorem S5_09CStatement_of_deps (h08A : ThLean.BP.S5.S5_08AStatement) :
    ThLean.BP.S5.S5_09CStatement := by
  classical
  intro V _ _ D r hr f hf
  by_cases hD : D = 0
  · subst D
    simp only [Nat.cast_zero, zero_mul]
    rw [poissonMixture_at_zero]
    simp [uniformMean]
  · have : Nonempty (Fin D) := ⟨⟨0, Nat.pos_of_ne_zero hD⟩⟩
    let t : ℝ := D * Fintype.card V * r
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hrate : t / Fintype.card (Fin D × V) = r := by
      have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
      have hV' : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      dsimp [t]
      simp [Fintype.card_prod, Fintype.card_fin, hD', hV']
    obtain ⟨C, hC⟩ := hf
    have hh := poisson_histogram_mean h08A (Fin D × V) t ht
      (fun c => f (fun v => ∑ a : Fin D, c (a, v))) ⟨C, fun c => hC _⟩
    rw [hrate] at hh
    calc
      _ = poissonMixture t (fun j => uniformMean
          (fun x : Fin j → Fin D × V => f (histogram (fun i => (x i).2)))) := by
        simpa only [histogram_projection] using hh
      _ = poissonMixture t (fun j => uniformMean
          (fun x : Fin j → V => f (histogram x))) := by
        unfold poissonMixture
        apply tsum_congr
        intro j
        exact congrArg (fun z : ℝ => poissonWeight t j * z)
          (cellProjection_uniformMean V D j (Nat.pos_of_ne_zero hD)
            (fun x => f (histogram x)))

example (h08A : ThLean.BP.S5.S5_08AStatement) : ThLean.BP.S5.S5_09CStatement :=
  S5_09CStatement_of_deps h08A

end ThLean.W.S551S

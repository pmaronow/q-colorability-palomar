import ThLean.BP.S4.Finite

noncomputable section
open scoped BigOperators
namespace ThLean.W.S401
open ThresholdFoundations

private theorem uniformMean_reindex {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (g : B → ℝ) :
    uniformMean (fun a => g (e a)) = uniformMean g := by
  unfold uniformMean
  have hs : (∑ a : A, g (e a)) = ∑ b : B, g b :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hs]
  rw [Fintype.card_congr e]

private theorem uniformMean_product {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (g : A × B → ℝ) :
    uniformMean g = uniformMean (fun a => uniformMean (fun b => g (a, b))) := by
  have ha : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›).ne'
  have hb : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty B›).ne'
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [Nat.cast_mul]
  rw [← Finset.sum_div]
  field_simp [ha, hb]

private def splitWords (E : Type) (r s : ℕ) :
    (Fin (r + s) → E) ≃ ((Fin r → E) × (Fin s → E)) :=
  (Equiv.arrowCongr (finSumFinEquiv.symm : Fin (r + s) ≃ Fin r ⊕ Fin s) (Equiv.refl E)).trans
    (Equiv.sumArrowEquivProdArrow (Fin r) (Fin s) E)

theorem S4_FIN_01CStatement_holds : ThLean.BP.S4.S4_FIN_01CStatement := by
  classical
  intro E _ hE r s f
  let A := Fin r → E
  let B := Fin s → E
  let e := splitWords E r s
  letI : Nonempty A := ⟨fun _ => Classical.choice hE⟩
  letI : Nonempty B := ⟨fun _ => Classical.choice hE⟩
  calc
    uniformMean (fun x : Fin (r + s) → E => f (fun i => x ⟨i.val, by omega⟩))
        = uniformMean (fun x : Fin (r + s) → E => f ((e x).1)) := by
          congr 1
    _ = uniformMean (fun p : A × B => f p.1) :=
          uniformMean_reindex e (fun p : A × B => f p.1)
    _ = uniformMean (fun a : A => uniformMean (fun _ : B => f a)) := by
          simpa using uniformMean_product (A := A) (B := B) (fun p : A × B => f p.1)
    _ = uniformMean f := by
          congr 1
          funext a
          simp [uniformMean]

end ThLean.W.S401

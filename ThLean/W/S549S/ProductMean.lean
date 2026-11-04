module

public import ThLean.BP.S5.Poisson

@[expose] public section

noncomputable section
open scoped BigOperators Topology

namespace ThLean.W.S549S
open ThresholdFoundations ThLean.BP.S5

def coordinateMass {I : Type} [Fintype I] (r : I → ℝ) (x : I → ℕ) : ℝ :=
  ∏ i, poissonWeight (r i) (x i)

def coordinateMean {I : Type} [Fintype I] (r : I → ℝ)
    (f : (I → ℕ) → ℝ) : ℝ := ∑' x, coordinateMass r x * f x

lemma poisson_summable (r : ℝ) : Summable (poissonWeight r) := by
  convert (Real.summable_pow_div_factorial r).mul_left (Real.exp (-r)) using 1
  ext n
  simp [poissonWeight, div_eq_mul_inv, mul_assoc]

lemma poisson_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ poissonWeight r n := by
  unfold poissonWeight
  positivity

lemma coordinateMass_nonneg {I : Type} [Fintype I] (r : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (x : I → ℕ) : 0 ≤ coordinateMass r x := by
  exact Finset.prod_nonneg fun i _ => poisson_nonneg (hr i) (x i)

lemma coordinateMass_summable (I : Type) [Fintype I] (r : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) : Summable (coordinateMass r) := by
  classical
  revert r
  refine Fintype.induction_empty_option (P := fun I inst => ∀ r : I → ℝ,
    (∀ i, 0 ≤ r i) → Summable (@coordinateMass I inst r)) ?_ ?_ ?_ I
  · intro I J _ e ih r hr
    let : Fintype I := Fintype.ofEquiv J e.symm
    let E : (I → ℕ) ≃ (J → ℕ) := e.arrowCongr (Equiv.refl ℕ)
    apply E.summable_iff.mp
    convert ih (fun i => r (e i)) (fun i => hr (e i)) using 1
    ext x
    simp only [Function.comp_apply, coordinateMass]
    exact (Fintype.prod_equiv e _ _ (fun i => by simp [E, Equiv.arrowCongr])).symm
  · intro r hr
    exact (hasSum_fintype _).summable
  · intro I _ ih r hr
    let E : (Option I → ℕ) ≃ ℕ × (I → ℕ) := Equiv.piOptionEquivProd
    apply E.symm.summable_iff.mp
    have hs := (poisson_summable (r none)).mul_of_nonneg
      (ih (fun i => r (some i)) (fun i => hr (some i)))
      (poisson_nonneg (hr none))
      (coordinateMass_nonneg _ (fun i => hr (some i)))
    convert hs using 1
    ext x
    simp [E, coordinateMass, Equiv.piOptionEquivProd]

lemma coordinateMean_equiv {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (r : J → ℝ) (f : (J → ℕ) → ℝ) :
    coordinateMean r f = coordinateMean (fun i => r (e i))
      (fun x => f (fun j => x (e.symm j))) := by
  classical
  let E : (I → ℕ) ≃ (J → ℕ) := e.arrowCongr (Equiv.refl ℕ)
  unfold coordinateMean
  rw [← E.tsum_eq]
  apply tsum_congr
  intro x
  have hmass : coordinateMass r (E x) = coordinateMass (fun i => r (e i)) x := by
    unfold coordinateMass
    exact (Fintype.prod_equiv e _ _ (fun i => by simp [E, Equiv.arrowCongr])).symm
  rw [hmass]
  rfl

lemma coordinateMean_sum {I J : Type} [Fintype I] [Fintype J]
    (r : I ⊕ J → ℝ) (hr : ∀ i, 0 ≤ r i) (f : (I ⊕ J → ℕ) → ℝ)
    (hf : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    coordinateMean r f =
      coordinateMean (fun i => r (Sum.inl i)) (fun x =>
        coordinateMean (fun j => r (Sum.inr j)) (fun y => f (Sum.elim x y))) := by
  classical
  obtain ⟨C, hC⟩ := hf
  let E := (Equiv.sumArrowEquivProdArrow I J ℕ).symm
  let w : (I → ℕ) × (J → ℕ) → ℝ := fun p =>
    coordinateMass (fun i => r (Sum.inl i)) p.1 *
    coordinateMass (fun j => r (Sum.inr j)) p.2
  have hw : ∀ p, 0 ≤ w p := fun p => mul_nonneg
    (coordinateMass_nonneg _ (fun i => hr (Sum.inl i)) p.1)
    (coordinateMass_nonneg _ (fun j => hr (Sum.inr j)) p.2)
  have hws : Summable w :=
    (coordinateMass_summable I _ (fun i => hr (Sum.inl i))).mul_of_nonneg
      (coordinateMass_summable J _ (fun j => hr (Sum.inr j)))
      (coordinateMass_nonneg _ (fun i => hr (Sum.inl i)))
      (coordinateMass_nonneg _ (fun j => hr (Sum.inr j)))
  have hs : Summable (fun p => w p * f (E p)) := by
    apply Summable.of_norm_bounded (hws.mul_right C)
    intro p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw p)]
    exact mul_le_mul_of_nonneg_left (hC _) (hw p)
  have hmass (p : (I → ℕ) × (J → ℕ)) : coordinateMass r (E p) = w p := by
    simp [coordinateMass, Fintype.prod_sum_type, E, w,
      Equiv.sumArrowEquivProdArrow]
  unfold coordinateMean
  rw [← E.tsum_eq]
  simp_rw [hmass]
  rw [hs.tsum_prod]
  apply tsum_congr
  intro x
  simp only [w, mul_assoc, tsum_mul_left]
  rfl

end ThLean.W.S549S

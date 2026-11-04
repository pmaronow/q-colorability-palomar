module

public import ThLean.BP.S3.Support
public import ThLean.BP.S3.Poisson

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S339
open ThresholdFoundations
open ThLean.BP.S3

universe u v

private def finFunEquivListLen {E : Type u} (k : ℕ) :
    (Fin k → E) ≃ {xs : List E // xs.length = k} where
  toFun x := ⟨List.ofFn x, by simp⟩
  invFun s := fun i => s.1.get ⟨i.val, by rw [s.2]; exact i.isLt⟩
  left_inv x := by
    funext i
    simp
  right_inv s := by
    apply Subtype.ext
    have h := List.ofFn_get s.1
    simpa [s.2] using h

private def listEquivSigmaLength (E : Type u) :
    List E ≃ (Σ k : ℕ, {xs : List E // xs.length = k}) where
  toFun xs := ⟨xs.length, ⟨xs, rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨k, ⟨xs, hxs⟩⟩
    subst k
    rfl

lemma weightedListMean_eq_listTsum {E : Type u} [Fintype E] [Nonempty E]
    (h31 : ThLean.BP.S3.S3_31Statement)
    (h32 : ThLean.BP.S3.S3_32Statement.{u})
    (ν : E → ℝ) (z : ℝ) (hν : IsProbabilityVector ν) (hz : 0 ≤ z)
    (f : List E → ℝ) (hf : ∀ xs, |f xs| ≤ 1) :
    weightedListMean z ν f = ∑' xs : List E, poissonListMass z ν xs * f xs := by
  classical
  rcases h32 E ν z hν hz with ⟨hMass, hTotal, hByLength, hWord⟩
  have hMassNonneg : ∀ xs, 0 ≤ poissonListMass z ν xs := by
    intro xs
    unfold poissonListMass
    have hprod : 0 ≤ (xs.map ν).prod := by
      induction xs with
      | nil => simp
      | cons a xs ih =>
          simp only [List.map_cons, List.prod_cons]
          exact mul_nonneg (hν.1 a) ih
    have hw := (h31 z hz).1 xs.length
    exact mul_nonneg hw hprod
  let F : List E → ℝ := fun xs => poissonListMass z ν xs * f xs
  have hF : Summable F := by
    apply Summable.of_norm_bounded hMass
    intro xs
    change ‖poissonListMass z ν xs * f xs‖ ≤ poissonListMass z ν xs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hMassNonneg xs)]
    calc
      poissonListMass z ν xs * |f xs| ≤ poissonListMass z ν xs * 1 :=
        mul_le_mul_of_nonneg_left (hf xs) (hMassNonneg xs)
      _ = poissonListMass z ν xs := by ring
  let σ := listEquivSigmaLength E
  have hSigma : Summable (fun p : (Σ k : ℕ, {xs : List E // xs.length = k}) =>
      F (σ.symm p)) := by
    exact (σ.symm.summable_iff).2 hF
  have hInner : ∀ k, Summable (fun s : {xs : List E // xs.length = k} => F s.1) := by
    intro k
    letI : Fintype {xs : List E // xs.length = k} :=
      Fintype.ofEquiv (Fin k → E) (finFunEquivListLen k)
    exact (hasSum_fintype (fun s : {xs : List E // xs.length = k} => F s.1)).summable
  unfold weightedListMean poissonMixture
  rw [← Equiv.tsum_eq σ.symm F, hSigma.tsum_sigma' hInner]
  apply tsum_congr
  intro k
  let e := finFunEquivListLen (E := E) k
  calc
    poissonWeight z k * ∑ x : Fin k → E,
        (∏ i, ν (x i)) * f (List.ofFn x) =
        ∑ x : Fin k → E, F (List.ofFn x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [F, hWord k x, mul_assoc]
    _ = ∑' x : Fin k → E, F (List.ofFn x) := by rw [tsum_fintype]
    _ = ∑' s : {xs : List E // xs.length = k}, F s.1 :=
      Equiv.tsum_eq e (fun s => F s.1)
    _ = ∑' s : {xs : List E // xs.length = k}, F (σ.symm ⟨k, s⟩) := by
      apply tsum_congr
      intro s
      rfl

private def fiberEquiv {α : Type u} {β : Type v} (g : α → β) :
    α ≃ (Σ b : β, {a : α // g a = b}) where
  toFun a := ⟨g a, ⟨a, rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨b, ⟨a, hab⟩⟩
    subst b
    rfl

lemma tsum_fiberwise_mul {α : Type u} {β : Type v}
    (a : α → ℝ) (g : α → β) (h : β → ℝ)
    (ha0 : ∀ x, 0 ≤ a x) (ha : Summable a) (hh : ∀ b, |h b| ≤ 1) :
    ∑' x, a x * h (g x) =
      ∑' b, (∑' x : {x : α // g x = b}, a x.val) * h b := by
  classical
  let F : α → ℝ := fun x => a x * h (g x)
  have hF : Summable F := by
    apply Summable.of_norm_bounded ha
    intro x
    change ‖a x * h (g x)‖ ≤ a x
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |a x| * |h (g x)| ≤ a x * 1 := by
        rw [abs_of_nonneg (ha0 x)]
        exact mul_le_mul_of_nonneg_left (hh (g x)) (ha0 x)
      _ = a x := by ring
  let e := fiberEquiv g
  have hSigma : Summable (fun p => F (e.symm p)) :=
    (e.symm.summable_iff).2 hF
  have hInner : ∀ b, Summable (fun x : {x : α // g x = b} => F x.val) := by
    intro b
    exact hF.subtype (fun x => g x = b)
  calc
    (∑' x, a x * h (g x)) = ∑' p, F (e.symm p) :=
      (Equiv.tsum_eq e.symm F).symm
    _ = ∑' b, ∑' x : {x : α // g x = b}, F (e.symm ⟨b, x⟩) :=
      hSigma.tsum_sigma' hInner
    _ = ∑' b, (∑' x : {x : α // g x = b}, a x.val) * h b := by
      apply tsum_congr
      intro b
      calc
        (∑' x : {x : α // g x = b}, F (e.symm ⟨b, x⟩)) =
            ∑' x : {x : α // g x = b}, a x.val * h b := by
          apply tsum_congr
          intro x
          simp [F, e, fiberEquiv, x.property]
        _ = (∑' x : {x : α // g x = b}, a x.val) * h b := by
          simpa only [Function.comp_apply] using
            (Summable.tsum_mul_right (h b) (ha.subtype (fun x => g x = b)))

end ThLean.W.S339

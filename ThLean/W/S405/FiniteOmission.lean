module

public import ThLean.BP.S4.Finite

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations

namespace ThLean.W.S405

private theorem uniformMean_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  classical
  unfold uniformMean
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  simp [Finset.sum_const, nsmul_eq_mul, hcard]

private theorem uniformMean_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

private theorem uniformMean_congr {A : Type} [Fintype A] {u v : A → ℝ}
    (h : ∀ a, u a = v a) : uniformMean u = uniformMean v := by
  have huv : u = v := funext h
  rw [huv]

private theorem uniformMean_fubini {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (F : A × B → ℝ) :
    uniformMean F = uniformMean (fun a => uniformMean (fun b => F (a, b))) := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, Finset.sum_div]
  field_simp [hA, hB]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  field_simp [hA, hB]

private theorem uniformMean_mono {A : Type} [Fintype A] (u v : A → ℝ)
    (h : ∀ a, u a ≤ v a) : uniformMean u ≤ uniformMean v := by
  classical
  by_cases hA : Nonempty A
  · have hcardNat : 0 < Fintype.card A := Fintype.card_pos_iff.mpr hA
    have hcard : 0 < (Fintype.card A : ℝ) := by exact_mod_cast hcardNat
    unfold uniformMean
    rw [div_le_div_iff_of_pos_right hcard]
    exact Finset.sum_le_sum (fun a _ => h a)
  · letI : IsEmpty A := ⟨fun a => hA ⟨a⟩⟩
    simp [uniformMean]

private theorem update_average
    (I E : Type) [Fintype I] [DecidableEq I] [Fintype E] [Nonempty E]
    (i : I) (H : (I → E) → ℝ) :
    uniformMean (fun x : I → E =>
      uniformMean (fun a : E => H (Function.update x i a))) = uniformMean H := by
  classical
  let X := I → E
  letI : Nonempty X := ⟨fun _ => Classical.choice (inferInstance : Nonempty E)⟩
  let e : (X × E) ≃ (X × E) :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := by
        rintro ⟨x, a⟩
        apply Prod.ext
        · funext j
          by_cases hji : j = i
          · subst j
            simp [Function.update]
          · simp [Function.update, hji]
        · simp [Function.update]
      right_inv := by
        rintro ⟨x, a⟩
        apply Prod.ext
        · funext j
          by_cases hji : j = i
          · subst j
            simp [Function.update]
          · simp [Function.update, hji]
        · simp [Function.update] }
  have hr := uniformMean_equiv e (fun p : X × E => H p.1)
  have hf := uniformMean_fubini (fun p : X × E => H (e p).1)
  have hf' : uniformMean (fun p : X × E => H (e p).1) =
      uniformMean (fun x : X =>
        uniformMean (fun a : E => H (Function.update x i a))) := by
    simpa [e] using hf
  have hproj : uniformMean (fun p : X × E => H p.1) = uniformMean H := by
    calc
      uniformMean (fun p : X × E => H p.1) =
          uniformMean (fun x : X => uniformMean (fun a : E => H x)) :=
        uniformMean_fubini (fun p : X × E => H p.1)
      _ = uniformMean H := by
        apply uniformMean_congr
        intro x
        exact uniformMean_const (H x)
  calc
    uniformMean (fun x : X =>
        uniformMean (fun a : E => H (Function.update x i a))) =
        uniformMean (fun p : X × E => H (e p).1) := hf'.symm
    _ = uniformMean (fun p : X × E => H p.1) := hr
    _ = uniformMean H := hproj

theorem S4_ES_04Statement_of_deps
    (h03 : ThLean.BP.S4.S4_ES_03Statement)
    (h01 : ThLean.BP.S4.S4_ES_01Statement) :
    ThLean.BP.S4.S4_ES_04Statement := by
  classical
  intro I E _ _ _ f g hinv
  by_cases hE : Nonempty E
  · letI : Nonempty E := hE
    have hfiber (i : I) (x : I → E) :
        variance (fun a : E => f (Function.update x i a)) ≤
          uniformMean (fun a : E => (f (Function.update x i a) - g i x) ^ 2) := by
      have hsquare := (h01 E (fun a : E => f (Function.update x i a)) (g i x)).1
      nlinarith [hsquare,
        sq_nonneg (uniformMean (fun a : E => f (Function.update x i a)) - g i x)]
    have havg (i : I) :
        uniformMean (fun x : I → E =>
          variance (fun a : E => f (Function.update x i a))) ≤
        uniformMean (fun x : I → E => (f x - g i x) ^ 2) := by
      calc
        uniformMean (fun x : I → E =>
            variance (fun a : E => f (Function.update x i a))) ≤
            uniformMean (fun x : I → E =>
              uniformMean (fun a : E =>
                (f (Function.update x i a) - g i x) ^ 2)) :=
          uniformMean_mono _ _ (fun x => hfiber i x)
        _ = uniformMean (fun x : I → E =>
              uniformMean (fun a : E =>
                (f (Function.update x i a) - g i (Function.update x i a)) ^ 2)) := by
          apply uniformMean_congr
          intro x
          apply uniformMean_congr
          intro a
          rw [hinv i x a]
        _ = uniformMean (fun x : I → E => (f x - g i x) ^ 2) :=
          update_average I E i (fun x => (f x - g i x) ^ 2)
    exact le_trans (h03 I E f)
      (Finset.sum_le_sum (fun i _ => havg i))
  · by_cases hI : Nonempty I
    · letI : Nonempty I := hI
      letI : IsEmpty (I → E) := ⟨fun x => hE ⟨x (Classical.choice hI)⟩⟩
      simp [variance, uniformMean]
    · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
      let x0 : I → E := fun i => isEmptyElim i
      letI : Nonempty (I → E) := ⟨x0⟩
      have hsub : Subsingleton (I → E) := ⟨fun x y => funext (fun i => isEmptyElim i)⟩
      have hfx : ∀ x : I → E, f x = f x0 :=
        fun x => congrArg f (hsub.elim x x0)
      have hmean : uniformMean f = f x0 := by
        calc
          uniformMean f = uniformMean (fun _ : I → E => f x0) :=
            uniformMean_congr hfx
          _ = f x0 := uniformMean_const (f x0)
      have hvar : variance f = 0 := by
        unfold variance
        rw [hmean]
        have hz : (fun x : I → E => (f x - f x0) ^ 2) = fun _ => 0 := by
          funext x
          rw [hfx x]
          simp
        rw [hz]
        exact uniformMean_const 0
      rw [hvar]
      simp

end ThLean.W.S405

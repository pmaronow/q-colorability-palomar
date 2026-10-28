import ThLean.BP.S3.Process

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

universe u
namespace ThLean.W.S309
open ThresholdFoundations ThLean.BP.S3

private noncomputable def coordinateEquiv
    {E : Type u} [Fintype E] {M k : ℕ} (ι : Fin k ↪ Fin M) :
    (Fin M → E) ≃ ((Fin k → E) × ({t : Fin M // t ∉ Set.range ι} → E)) := by
  classical
  refine
    { toFun := fun y => (fun i => y (ι i), fun t => y t.1)
      invFun := fun p t => if h : t ∈ Set.range ι then p.1 (Classical.choose h)
        else p.2 ⟨t, h⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    funext t
    by_cases h : t ∈ Set.range ι
    · simp only [dite_eq_left h]
      change y (ι (Classical.choose h)) = y t
      rw [Classical.choose_spec h]
    · simp [h]
  · intro p
    apply Prod.ext
    · funext i
      have h : ι i ∈ Set.range ι := ⟨i, rfl⟩
      simp only [dite_eq_left h]
      have hh : ι (Classical.choose h) = ι i := by simp
      have hc : Classical.choose h = i := ι.injective hh
      rw [hc]
    · funext t
      simp [t.property]

private theorem coordinate_card
    {E : Type u} [Fintype E] {M k : ℕ} (ι : Fin k ↪ Fin M) :
    Fintype.card (Fin M → E) =
      Fintype.card (Fin k → E) * Fintype.card ({t : Fin M // t ∉ Set.range ι} → E) := by
  classical
  rw [Fintype.card_congr (coordinateEquiv (E := E) ι), Fintype.card_prod]

private theorem uniformMeanENN_coordinate
    {E : Type u} [Fintype E] [Nonempty E] {M k : ℕ}
    (ι : Fin k ↪ Fin M) (F : (Fin k → E) → ℝ≥0∞) :
    uniformMeanENN (fun y : Fin M → E => F (fun i => y (ι i))) = uniformMeanENN F := by
  classical
  let S := {t : Fin M // t ∉ Set.range ι}
  let A := Fin k → E
  let B := S → E
  have hsum :
      (∑ y : Fin M → E, F (fun i => y (ι i))) =
        ∑ p : A × B, F p.1 := by
    simpa [coordinateEquiv, A, B, S] using
      (Equiv.sum_comp (coordinateEquiv (E := E) ι) (fun p : A × B => F p.1))
  have hnum : (∑ p : A × B, F p.1) =
      (Fintype.card B : ℝ≥0∞) * ∑ a : A, F a := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hcard : Fintype.card (Fin M → E) = Fintype.card A * Fintype.card B := by
    simpa [A, B, S] using coordinate_card (E := E) ι
  have hb0 : (Fintype.card B : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  have hbtop : (Fintype.card B : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  unfold uniformMeanENN
  rw [hsum, hnum, hcard]
  simp only [Nat.cast_mul]
  calc
    (Fintype.card B : ℝ≥0∞) * (∑ a : A, F a) /
        ((Fintype.card A : ℝ≥0∞) * (Fintype.card B : ℝ≥0∞)) =
      ((∑ a : A, F a) / (Fintype.card A : ℝ≥0∞)) := by
        rw [mul_comm (Fintype.card B : ℝ≥0∞) (∑ a : A, F a)]
        exact ENNReal.mul_div_mul_right _ _ hb0 hbtop
    _ = uniformMeanENN F := by rfl

private theorem uniformMean_coordinate
    {E : Type u} [Fintype E] [Nonempty E] {M k : ℕ}
    (ι : Fin k ↪ Fin M) (F : (Fin k → E) → ℝ) :
    uniformMean (fun y : Fin M → E => F (fun i => y (ι i))) = uniformMean F := by
  classical
  let S := {t : Fin M // t ∉ Set.range ι}
  let A := Fin k → E
  let B := S → E
  have hsum :
      (∑ y : Fin M → E, F (fun i => y (ι i))) =
        ∑ p : A × B, F p.1 := by
    simpa [coordinateEquiv, A, B, S] using
      (Equiv.sum_comp (coordinateEquiv (E := E) ι) (fun p : A × B => F p.1))
  have hnum : (∑ p : A × B, F p.1) =
      (Fintype.card B : ℝ) * ∑ a : A, F a := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hcard : Fintype.card (Fin M → E) = Fintype.card A * Fintype.card B := by
    simpa [A, B, S] using coordinate_card (E := E) ι
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  have hB0 : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  have hAcard : Fintype.card A = Fintype.card (Fin k → E) := rfl
  unfold uniformMean
  rw [hsum, hnum, hcard]
  rw [← hAcard]
  simp only [Nat.cast_mul]
  field_simp
  rfl

private theorem uniformMeanENN_prod
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → ℝ≥0∞) (g : B → ℝ≥0∞) :
    uniformMeanENN (fun p : A × B => f p.1 * g p.2) =
      uniformMeanENN f * uniformMeanENN g := by
  classical
  have hsum : (∑ p : A × B, f p.1 * g p.2) =
      (∑ a : A, f a) * ∑ b : B, g b := by
    rw [Fintype.sum_prod_type]
    exact (Fintype.sum_mul_sum f g).symm
  unfold uniformMeanENN
  rw [hsum, Fintype.card_prod]
  rw [Nat.cast_mul]
  exact ENNReal.mul_div_mul_comm
    (Or.inr (ENNReal.natCast_ne_top (Fintype.card B)))
    (Or.inl (ENNReal.natCast_ne_top (Fintype.card A)))

private noncomputable def finFunctionEquiv
    {E : Type u} (a b : ℕ) :
    (Fin (a+b) → E) ≃ ((Fin a → E) × (Fin b → E)) :=
  ((Equiv.arrowCongr (finSumFinEquiv (m := a) (n := b)) (Equiv.refl E)).symm).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) E)

private theorem finFunctionEquiv_apply
    {E : Type u} (a b : ℕ) (x : Fin (a+b) → E) :
    finFunctionEquiv (E := E) a b x =
      (fun i => x (Fin.castAdd b i), fun j => x (Fin.natAdd a j)) := by
  ext i <;> simp [finFunctionEquiv]

private def disjointSumEmbedding
    {M a b : ℕ} (i : Fin a ↪ Fin M) (j : Fin b ↪ Fin M)
    (h : Disjoint (Set.range i) (Set.range j)) : (Fin a ⊕ Fin b) ↪ Fin M :=
  { toFun := Sum.elim i j
    inj' := by
      intro x y hxy
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (i.injective hxy)
        | inr y =>
          have hnot : i x ∉ Set.range j := Set.disjoint_left.mp h ⟨x, rfl⟩
          exact False.elim (hnot ⟨y, hxy.symm⟩)
      | inr x =>
        cases y with
        | inl y =>
          have hnot : j x ∉ Set.range i := Set.disjoint_right.mp h ⟨x, rfl⟩
          exact False.elim (hnot ⟨y, hxy.symm⟩)
        | inr y => exact congrArg Sum.inr (j.injective hxy) }

private def disjointFinEmbedding
    {M a b : ℕ} (i : Fin a ↪ Fin M) (j : Fin b ↪ Fin M)
    (h : Disjoint (Set.range i) (Set.range j)) : Fin (a+b) ↪ Fin M :=
  finSumFinEquiv.symm.toEmbedding.trans (disjointSumEmbedding i j h)

private theorem uniformMeanENN_finSum
    {E : Type u} [Fintype E] [Nonempty E] (a b : ℕ)
    (f : (Fin a → E) → ℝ≥0∞) (g : (Fin b → E) → ℝ≥0∞) :
    uniformMeanENN (fun x : Fin (a+b) → E =>
      f (fun i => x (Fin.castAdd b i)) * g (fun j => x (Fin.natAdd a j))) =
        uniformMeanENN f * uniformMeanENN g := by
  let e := finFunctionEquiv (E := E) a b
  have hsum :
      (∑ x : Fin (a+b) → E,
        f (fun i => x (Fin.castAdd b i)) * g (fun j => x (Fin.natAdd a j))) =
      ∑ p : (Fin a → E) × (Fin b → E), f p.1 * g p.2 := by
    calc
      (∑ x : Fin (a+b) → E,
          f (fun i => x (Fin.castAdd b i)) * g (fun j => x (Fin.natAdd a j))) =
        ∑ x : Fin (a+b) → E, f (e x).1 * g (e x).2 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [e, finFunctionEquiv_apply]
      _ = ∑ p : (Fin a → E) × (Fin b → E), f p.1 * g p.2 :=
        Equiv.sum_comp e (fun p : (Fin a → E) × (Fin b → E) => f p.1 * g p.2)
  have hcard : Fintype.card (Fin (a+b) → E) =
      Fintype.card ((Fin a → E) × (Fin b → E)) := Fintype.card_congr e
  calc
    uniformMeanENN (fun x : Fin (a+b) → E =>
        f (fun i => x (Fin.castAdd b i)) * g (fun j => x (Fin.natAdd a j))) =
      uniformMeanENN (fun p : (Fin a → E) × (Fin b → E) => f p.1 * g p.2) := by
        unfold uniformMeanENN
        rw [hsum, hcard]
    _ = uniformMeanENN f * uniformMeanENN g := uniformMeanENN_prod f g

theorem S3_02Statement_holds : ThLean.BP.S3.S3_02Statement := by
  intro E hE hNonempty M k ι
  classical
  constructor
  · intro x
    let P : (Fin k → E) → Prop := fun z => ∀ j, z j = x j
    have hmean := uniformMean_coordinate (E := E) ι (fun z => indicator (P z))
    have hsum : (∑ z : Fin k → E, indicator (P z)) = 1 := by
      have hP (z : Fin k → E) : P z ↔ z = x := by
        constructor
        · intro hz
          funext j
          exact hz j
        · intro hz j
          simp [hz]
      simp [P, indicator, hP]
    have hprob : uniformMean (fun z : Fin k → E => indicator (P z)) =
        1 / (Fintype.card (Fin k → E) : ℝ) := by
      unfold uniformMean
      rw [hsum]
    calc
      uniformProb (fun y : Fin M → E => ∀ j, y (ι j) = x j) =
          uniformMean (fun y : Fin M → E => indicator (P (fun j => y (ι j)))) := rfl
      _ = uniformMean (fun z : Fin k → E => indicator (P z)) := hmean
      _ = 1 / (Fintype.card (Fin k → E) : ℝ) := hprob
      _ = (Fintype.card E : ℝ)^(-(k : ℤ)) := by
        rw [Fintype.card_pi_const, Nat.cast_pow]
        rw [zpow_neg, zpow_natCast]
        simp [one_div]
  constructor
  · intro F
    exact uniformMeanENN_coordinate ι F
  constructor
  · intro F
    exact uniformMean_coordinate ι F
  · intro a b i j hdis f g
    let ι' := disjointFinEmbedding i j hdis
    let F : (Fin (a+b) → E) → ℝ≥0∞ := fun x =>
      f (fun r => x (Fin.castAdd b r)) * g (fun r => x (Fin.natAdd a r))
    have htransport :
        uniformMeanENN (fun y : Fin M → E =>
          f (fun r => y (i r)) * g (fun r => y (j r))) =
        uniformMeanENN (fun y : Fin M → E => F (fun t => y (ι' t))) := by
      congr 1
      funext y
      simp [F, ι', disjointFinEmbedding, disjointSumEmbedding,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      rfl
    calc
      uniformMeanENN (fun y : Fin M → E =>
          f (fun r => y (i r)) * g (fun r => y (j r))) =
        uniformMeanENN (fun y : Fin M → E => F (fun t => y (ι' t))) := htransport
      _ = uniformMeanENN F := uniformMeanENN_coordinate ι' F
      _ = uniformMeanENN f * uniformMeanENN g := uniformMeanENN_finSum a b f g

end ThLean.W.S309

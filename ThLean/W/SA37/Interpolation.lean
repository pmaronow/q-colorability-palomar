module

public import ThLean.BP.SA.Interpolation

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA37
open ThLean.BP.SA
open ThresholdFoundations

private def coordSlope (n₁ n₂ : ℕ) (j : Fin 3)
    (m : InterpolationMark n₁ n₂) : ℝ :=
  match m with
  | .inl _ => if j = 0 then 1 / ((n₁ + n₂ : ℕ) : ℝ)^2 else 0
  | .inr (.inl _) => if j = 1 then 1 / (n₁ : ℝ)^2 else 0
  | .inr (.inr _) => if j = 2 then 1 / (n₂ : ℝ)^2 else 0

private def coordBase (n₁ n₂ : ℕ) (μ : Fin 3 → ℝ) (j : Fin 3)
    (m : InterpolationMark n₁ n₂) : ℝ :=
  match m with
  | .inl _ => if j = 0 then 0 else μ 0 / ((n₁ + n₂ : ℕ) : ℝ)^2
  | .inr (.inl _) => if j = 1 then 0 else μ 1 / (n₁ : ℝ)^2
  | .inr (.inr _) => if j = 2 then 0 else μ 2 / (n₂ : ℝ)^2

private theorem coordIncrement_eq_addLoss
    (h12b : SA_I12bStatement) (h16a : SA_I16aStatement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (μ : Fin 3 → ℝ) (hμ : ∀ i, 0 ≤ μ i) (j : Fin 3) :
    (∑ m : InterpolationMark n₁ n₂,
      coordSlope n₁ n₂ j m *
        supportMean (fun T =>
          indicator (Colorable q (supportGraph interpolationMarkEdge (insert m T))) -
            indicator (Colorable q (supportGraph interpolationMarkEdge T)))
          (markRate n₁ n₂ μ)) =
      -supportMean (fun T => addLoss q n₁ n₂ j (supportGraph T))
        (markRate n₁ n₂ μ) := by
  classical
  let D := InterpolationMark n₁ n₂
  let F : Finset D → ℝ := fun T =>
    indicator (Colorable q (supportGraph interpolationMarkEdge T))
  let α : D → ℝ := coordSlope n₁ n₂ j
  let β : D → ℝ := coordBase n₁ n₂ μ j
  have hrates : ∀ t : ℝ,
      markRate n₁ n₂ (Function.update μ j t) = fun m => α m * t + β m := by
    intro t
    funext m
    fin_cases j <;> cases m with
    | inl p => simp [α, β, coordSlope, coordBase, interpolationMarkRate, Function.update] <;> ring
    | inr s => cases s with
      | inl p => simp [α, β, coordSlope, coordBase, interpolationMarkRate, Function.update] <;> ring
      | inr p => simp [α, β, coordSlope, coordBase, interpolationMarkRate, Function.update] <;> ring
  have hpath :
      (fun t => finiteChiBar q n₁ n₂ (Function.update μ j t)) =
        (fun t => supportMean F (fun m => α m * t + β m)) := by
    funext t
    change supportMean F (markRate n₁ n₂ (Function.update μ j t)) =
      supportMean F (fun m => α m * t + β m)
    rw [hrates t]
  have h12 := h12b D F α β
  have h12der : HasDerivAt (fun t => supportMean F (fun m => α m * t + β m))
      (∑ m, α m * supportMean (fun T => F (insert m T) - F T)
        (fun m => α m * (μ j) + β m)) (μ j) := h12.2 (μ j)
  have hsame : (fun m => α m * (μ j) + β m) = markRate n₁ n₂ μ := by
    rw [← hrates (μ j)]
    funext m
    simp
  rw [hsame] at h12der
  have h16 := h16a q n₁ n₂ hq hn₁ hn₂ μ hμ j
  rw [hpath] at h16
  have heq := h12der.unique h16
  simpa [D, F, α] using heq

private theorem interpolationDerivative_addLoss
    (h12b : SA_I12bStatement) (h16a : SA_I16aStatement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (c θ : ℝ) (hθ : θ ∈ Set.Icc 0 c) :
    HasDerivAt (fun t => finiteChi q n₁ n₂ c t)
      (-((n₁ + n₂ : ℕ) : ℝ) *
          supportMean (fun T => addLoss q n₁ n₂ 0 (supportGraph T))
            (markRate n₁ n₂ (interpolationMeans n₁ n₂ c θ)) +
        (n₁ : ℝ) *
          supportMean (fun T => addLoss q n₁ n₂ 1 (supportGraph T))
            (markRate n₁ n₂ (interpolationMeans n₁ n₂ c θ)) +
        (n₂ : ℝ) *
          supportMean (fun T => addLoss q n₁ n₂ 2 (supportGraph T))
            (markRate n₁ n₂ (interpolationMeans n₁ n₂ c θ))) θ := by
  classical
  let D := InterpolationMark n₁ n₂
  let F : Finset D → ℝ := fun T =>
    indicator (Colorable q (supportGraph interpolationMarkEdge T))
  let μ : Fin 3 → ℝ := interpolationMeans n₁ n₂ c θ
  rcases hθ with ⟨hθ0, hθc⟩
  have hct : 0 ≤ c - θ := sub_nonneg.mpr hθc
  have hμ : ∀ i, 0 ≤ μ i := by
    intro i
    fin_cases i <;> simp [μ, interpolationMeans] <;> positivity
  let s0 : D → ℝ := coordSlope n₁ n₂ 0
  let s1 : D → ℝ := coordSlope n₁ n₂ 1
  let s2 : D → ℝ := coordSlope n₁ n₂ 2
  let α : D → ℝ := fun m =>
    ((n₁ + n₂ : ℕ) : ℝ) * s0 m - (n₁ : ℝ) * s1 m - (n₂ : ℝ) * s2 m
  let β : D → ℝ := fun m => match m with
    | .inl _ => 0
    | .inr (.inl _) => (n₁ : ℝ) * c / (n₁ : ℝ)^2
    | .inr (.inr _) => (n₂ : ℝ) * c / (n₂ : ℝ)^2
  have hrates : ∀ t : ℝ,
      markRate n₁ n₂ (interpolationMeans n₁ n₂ c t) = fun m => α m * t + β m := by
    intro t
    funext m
    cases m with
    | inl p => simp [α, β, s0, s1, s2, coordSlope, interpolationMarkRate,
        interpolationMeans] <;> ring
    | inr s => cases s with
      | inl p => simp [α, β, s0, s1, s2, coordSlope,
          interpolationMarkRate, interpolationMeans] <;> ring
      | inr p => simp [α, β, s0, s1, s2, coordSlope,
          interpolationMarkRate, interpolationMeans] <;> ring
  have hpath : (fun t => finiteChi q n₁ n₂ c t) =
      fun t => supportMean F (fun m => α m * t + β m) := by
    funext t
    change supportMean F (markRate n₁ n₂ (interpolationMeans n₁ n₂ c t)) = _
    rw [hrates t]
  have h12 := h12b D F α β
  have hder : HasDerivAt (fun t => finiteChi q n₁ n₂ c t)
      (∑ m, α m * supportMean (fun T => F (insert m T) - F T)
        (fun m => α m * θ + β m)) θ := by
    rw [hpath]
    exact h12.2 θ
  have hrateθ : (fun m => α m * θ + β m) = markRate n₁ n₂ μ := by
    rw [← hrates θ]
  rw [hrateθ] at hder
  have h0 := coordIncrement_eq_addLoss h12b h16a q n₁ n₂ hq hn₁ hn₂ μ hμ 0
  have h1 := coordIncrement_eq_addLoss h12b h16a q n₁ n₂ hq hn₁ hn₂ μ hμ 1
  have h2 := coordIncrement_eq_addLoss h12b h16a q n₁ n₂ hq hn₁ hn₂ μ hμ 2
  let X : D → ℝ := fun m => supportMean (fun T => F (insert m T) - F T)
    (markRate n₁ n₂ μ)
  have hsum : (∑ m, α m * X m) =
      ((n₁ + n₂ : ℕ) : ℝ) * (∑ m, s0 m * X m) -
        (n₁ : ℝ) * (∑ m, s1 m * X m) - (n₂ : ℝ) * (∑ m, s2 m * X m) := by
    calc
      (∑ m, α m * X m) =
          ∑ m, (((n₁ + n₂ : ℕ) : ℝ) * (s0 m * X m) -
            (n₁ : ℝ) * (s1 m * X m) - (n₂ : ℝ) * (s2 m * X m)) := by
        apply Finset.sum_congr rfl
        intro m hm
        simp [α, s0, s1, s2]
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  have h0' : (∑ m, s0 m * X m) =
      -supportMean (fun T => addLoss q n₁ n₂ 0 (supportGraph T))
        (markRate n₁ n₂ μ) := by
    change (∑ m, coordSlope n₁ n₂ 0 m *
      supportMean (fun T =>
        indicator (Colorable q (supportGraph interpolationMarkEdge (insert m T))) -
          indicator (Colorable q (supportGraph interpolationMarkEdge T)))
        (markRate n₁ n₂ μ)) = _
    exact h0
  have h1' : (∑ m, s1 m * X m) =
      -supportMean (fun T => addLoss q n₁ n₂ 1 (supportGraph T))
        (markRate n₁ n₂ μ) := by
    change (∑ m, coordSlope n₁ n₂ 1 m *
      supportMean (fun T =>
        indicator (Colorable q (supportGraph interpolationMarkEdge (insert m T))) -
          indicator (Colorable q (supportGraph interpolationMarkEdge T)))
        (markRate n₁ n₂ μ)) = _
    exact h1
  have h2' : (∑ m, s2 m * X m) =
      -supportMean (fun T => addLoss q n₁ n₂ 2 (supportGraph T))
        (markRate n₁ n₂ μ) := by
    change (∑ m, coordSlope n₁ n₂ 2 m *
      supportMean (fun T =>
        indicator (Colorable q (supportGraph interpolationMarkEdge (insert m T))) -
          indicator (Colorable q (supportGraph interpolationMarkEdge T)))
        (markRate n₁ n₂ μ)) = _
    exact h2
  have hsum' : (∑ m, α m * X m) =
      -((n₁ + n₂ : ℕ) : ℝ) *
          supportMean (fun T => addLoss q n₁ n₂ 0 (supportGraph T))
            (markRate n₁ n₂ μ) +
        (n₁ : ℝ) *
          supportMean (fun T => addLoss q n₁ n₂ 1 (supportGraph T))
            (markRate n₁ n₂ μ) +
        (n₂ : ℝ) *
          supportMean (fun T => addLoss q n₁ n₂ 2 (supportGraph T))
            (markRate n₁ n₂ μ) := by
    rw [hsum, h0', h1', h2']
    ring
  have hderX : HasDerivAt (fun t => finiteChi q n₁ n₂ c t)
      (∑ m, α m * X m) θ := by
    simpa [X] using hder
  rw [hsum'] at hderX
  exact hderX

private def insertionLoss {V : Type} [Fintype V]
    (q : ℕ) (G : MGraph V) (e : Sym2 V) : ℝ :=
  indicator (Colorable q G ∧ ¬ Colorable q (addEdge G e))

private theorem indicator_sub_eq_insertionLoss {V : Type} [Fintype V]
    (q : ℕ) (G : MGraph V) (e : Sym2 V) :
    indicator (Colorable q G) - indicator (Colorable q (addEdge G e)) =
      insertionLoss q G e := by
  have hmono : Colorable q (addEdge G e) → Colorable q G := by
    rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro u v huv
    apply hσ u v
    by_cases he : s(u, v) = e
    · simpa [addEdge, he] using (show 0 < G (s(u, v)) + 1 by omega)
    · simpa [addEdge, he] using huv
  by_cases hG : Colorable q G
  · by_cases hA : Colorable q (addEdge G e) <;>
      simp [indicator, insertionLoss, hG, hA]
  · have hA : ¬ Colorable q (addEdge G e) := fun h => hG (hmono h)
    simp [indicator, insertionLoss, hG, hA]

private def leftBlock (n₁ n₂ : ℕ) : Finset (Fin (n₁ + n₂)) :=
  Finset.univ.image (leftVertex n₁ n₂)

private def rightBlock (n₁ n₂ : ℕ) : Finset (Fin (n₁ + n₂)) :=
  Finset.univ.image (rightVertex n₁ n₂)

private theorem leftBlock_eq_filter (n₁ n₂ : ℕ) :
    leftBlock n₁ n₂ = Finset.univ.filter (fun v : Fin (n₁ + n₂) => v.val < n₁) := by
  classical
  ext v
  simp only [leftBlock, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_filter, Finset.mem_univ]
  constructor
  · rintro ⟨u, hu⟩
    have heq : u.val = v.val := by
      simpa [leftVertex] using congrArg Fin.val hu
    omega
  · intro hv
    refine ⟨⟨v.val, hv⟩, ?_⟩
    exact Fin.ext rfl

private theorem rightBlock_eq_filter (n₁ n₂ : ℕ) :
    rightBlock n₁ n₂ = Finset.univ.filter (fun v : Fin (n₁ + n₂) => n₁ ≤ v.val) := by
  classical
  ext v
  simp only [rightBlock, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_filter, Finset.mem_univ]
  constructor
  · rintro ⟨u, hu⟩
    have hv := congrArg Fin.val hu
    simp [rightVertex] at hv
    omega
  · intro hv
    have hval : v.val - n₁ < n₂ := by omega
    refine ⟨⟨v.val - n₁, hval⟩, ?_⟩
    apply Fin.ext
    simp [rightVertex]
    omega

private theorem leftVertex_injective (n₁ n₂ : ℕ) :
    Function.Injective (leftVertex n₁ n₂) := by
  intro x y h
  exact Fin.ext (by simpa [leftVertex] using congrArg Fin.val h)

private theorem rightVertex_injective (n₁ n₂ : ℕ) :
    Function.Injective (rightVertex n₁ n₂) := by
  intro x y h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [rightVertex] at hv
  omega

private theorem sum_leftBlock_reindex {n₁ n₂ : ℕ} (f : Fin (n₁+n₂) → Fin (n₁+n₂) → ℝ) :
    (∑ x ∈ leftBlock n₁ n₂, ∑ y ∈ leftBlock n₁ n₂, f x y) =
      ∑ x : Fin n₁, ∑ y : Fin n₁,
        f (leftVertex n₁ n₂ x) (leftVertex n₁ n₂ y) := by
  classical
  simp only [leftBlock]
  simp only [Finset.sum_image (leftVertex_injective n₁ n₂).injOn]

private theorem sum_rightBlock_reindex {n₁ n₂ : ℕ} (f : Fin (n₁+n₂) → Fin (n₁+n₂) → ℝ) :
    (∑ x ∈ rightBlock n₁ n₂, ∑ y ∈ rightBlock n₁ n₂, f x y) =
      ∑ x : Fin n₂, ∑ y : Fin n₂,
        f (rightVertex n₁ n₂ x) (rightVertex n₁ n₂ y) := by
  classical
  simp only [rightBlock]
  simp only [Finset.sum_image (rightVertex_injective n₁ n₂).injOn]

private theorem orderedLoss_count (h14b : SA_I14bStatement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (G : MGraph (Fin (n₁+n₂)))
    (T : Finset (Fin (n₁+n₂))) :
    (∑ x ∈ T, ∑ y ∈ T, insertionLoss q G (s(x, y))) =
      if Colorable q G then
        ∑ C ∈ frozenClasses q G, ((C ∩ T).card : ℝ)^2 else 0 := by
  classical
  let classicalEq : DecidableEq (Fin (n₁+n₂)) :=
    fun a b => Classical.propDecidable (a = b)
  let standardEq : DecidableEq (Fin (n₁+n₂)) := instDecidableEqFin _
  let classicalInter (C : Finset (Fin (n₁+n₂))) :=
    @Inter.inter (Finset (Fin (n₁+n₂))) (@Finset.instInter _ classicalEq) C T
  let standardInter (C : Finset (Fin (n₁+n₂))) :=
    @Inter.inter (Finset (Fin (n₁+n₂))) (@Finset.instInter _ standardEq) C T
  have hraw : (∑ x ∈ T, ∑ y ∈ T, insertionLoss q G (s(x, y))) =
      if Colorable q G then
        ∑ C ∈ frozenClasses q G, ((classicalInter C).card : ℝ)^2 else 0 := by
    simpa only [indicator_sub_eq_insertionLoss, classicalInter] using
      h14b _ q G T hq
  have hInter (C : Finset (Fin (n₁+n₂))) : classicalInter C = standardInter C := by
    ext x
    simp [classicalInter, standardInter]
  change (∑ x ∈ T, ∑ y ∈ T, insertionLoss q G (s(x, y))) =
      if Colorable q G then
        ∑ C ∈ frozenClasses q G, ((standardInter C).card : ℝ)^2 else 0
  rw [hraw]
  by_cases hcol : Colorable q G
  · simp only [if_pos hcol]
    apply Finset.sum_congr rfl
    intro C hC
    rw [hInter]
  · simp [hcol]

private theorem loss0_formula (h14b : SA_I14bStatement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (G : MGraph (Fin (n₁+n₂))) :
    addLoss q n₁ n₂ 0 G =
      (if Colorable q G then
        ∑ C ∈ frozenClasses q G, (C.card : ℝ)^2 else 0) /
          ((n₁ + n₂ : ℕ) : ℝ)^2 := by
  classical
  have hcount := orderedLoss_count h14b q n₁ n₂ hq G Finset.univ
  have hmean : addLoss q n₁ n₂ 0 G =
      (∑ x : Fin (n₁+n₂), ∑ y : Fin (n₁+n₂), insertionLoss q G (s(x,y))) /
        ((n₁+n₂ : ℕ) : ℝ)^2 := by
    simp [addLoss, uniformMean, insertionLoss, Fintype.sum_prod_type,
      Fintype.card_prod, Fintype.card_fin, Nat.cast_add] <;> ring
  rw [hmean, hcount]
  simp [Finset.inter_univ]

private theorem loss1_formula (h14b : SA_I14bStatement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (G : MGraph (Fin (n₁+n₂))) :
    addLoss q n₁ n₂ 1 G =
      (if Colorable q G then
        ∑ C ∈ frozenClasses q G,
          ((C.filter (fun v => v.val < n₁)).card : ℝ)^2 else 0) /
          (n₁ : ℝ)^2 := by
  classical
  have hcount := orderedLoss_count h14b q n₁ n₂ hq G (leftBlock n₁ n₂)
  rw [sum_leftBlock_reindex] at hcount
  have hcount' : (∑ x : Fin n₁, ∑ y : Fin n₁,
        insertionLoss q G (s(leftVertex n₁ n₂ x, leftVertex n₁ n₂ y))) =
      if Colorable q G then
        ∑ C ∈ frozenClasses q G,
          ((C.filter (fun v => v.val < n₁)).card : ℝ)^2 else 0 := by
    simpa [leftBlock_eq_filter, Finset.inter_filter] using hcount
  have hmean : addLoss q n₁ n₂ 1 G =
      (∑ x : Fin n₁, ∑ y : Fin n₁,
        insertionLoss q G (s(leftVertex n₁ n₂ x, leftVertex n₁ n₂ y))) /
          (n₁ : ℝ)^2 := by
    simp [addLoss, uniformMean, insertionLoss, Fintype.sum_prod_type,
      Fintype.card_prod, Fintype.card_fin] <;> ring
  rw [hmean, hcount']

private theorem loss2_formula (h14b : SA_I14bStatement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (G : MGraph (Fin (n₁+n₂))) :
    addLoss q n₁ n₂ 2 G =
      (if Colorable q G then
        ∑ C ∈ frozenClasses q G,
          ((C.filter (fun v => n₁ ≤ v.val)).card : ℝ)^2 else 0) /
          (n₂ : ℝ)^2 := by
  classical
  have hcount := orderedLoss_count h14b q n₁ n₂ hq G (rightBlock n₁ n₂)
  rw [sum_rightBlock_reindex] at hcount
  have hcount' : (∑ x : Fin n₂, ∑ y : Fin n₂,
        insertionLoss q G (s(rightVertex n₁ n₂ x, rightVertex n₁ n₂ y))) =
      if Colorable q G then
        ∑ C ∈ frozenClasses q G,
          ((C.filter (fun v => n₁ ≤ v.val)).card : ℝ)^2 else 0 := by
    simpa [rightBlock_eq_filter, Finset.inter_filter] using hcount
  have hmean : addLoss q n₁ n₂ 2 G =
      (∑ x : Fin n₂, ∑ y : Fin n₂,
        insertionLoss q G (s(rightVertex n₁ n₂ x, rightVertex n₁ n₂ y))) /
          (n₂ : ℝ)^2 := by
    simp [addLoss, uniformMean, insertionLoss, Fintype.sum_prod_type,
      Fintype.card_prod, Fintype.card_fin] <;> ring
  rw [hmean, hcount']

private theorem lossCombo_eq_drift (h14b : SA_I14bStatement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (G : MGraph (Fin (n₁+n₂))) :
    -((n₁+n₂ : ℕ) : ℝ) * addLoss q n₁ n₂ 0 G +
        (n₁ : ℝ) * addLoss q n₁ n₂ 1 G +
        (n₂ : ℝ) * addLoss q n₁ n₂ 2 G =
      interpolationClassDrift q n₁ n₂ G := by
  classical
  have h0 := loss0_formula h14b q n₁ n₂ hq G
  have h1 := loss1_formula h14b q n₁ n₂ hq G
  have h2 := loss2_formula h14b q n₁ n₂ hq G
  by_cases hcol : Colorable q G
  · rw [h0, h1, h2]
    simp only [if_pos hcol]
    have hn₁R : (n₁ : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n₁))
    have hn₂R : (n₂ : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n₂))
    have hNR : ((n₁+n₂ : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n₁+n₂))
    let Cset := frozenClasses q G
    let S₀ : ℝ := ∑ C ∈ Cset, (C.card : ℝ)^2
    let S₁ : ℝ := ∑ C ∈ Cset, ((C.filter (fun v => v.val < n₁)).card : ℝ)^2
    let S₂ : ℝ := ∑ C ∈ Cset, ((C.filter (fun v => n₁ ≤ v.val)).card : ℝ)^2
    have hscale :
        -((n₁+n₂ : ℕ) : ℝ) * (S₀ / ((n₁+n₂ : ℕ) : ℝ)^2) +
            (n₁ : ℝ) * (S₁ / (n₁ : ℝ)^2) +
            (n₂ : ℝ) * (S₂ / (n₂ : ℝ)^2) =
          S₁ / (n₁ : ℝ) + S₂ / (n₂ : ℝ) - S₀ / ((n₁+n₂ : ℕ) : ℝ) := by
      field_simp [hn₁R, hn₂R, hNR]
      ring
    have hsum :
        S₁ / (n₁ : ℝ) + S₂ / (n₂ : ℝ) - S₀ / ((n₁+n₂ : ℕ) : ℝ) =
          ∑ C ∈ Cset,
            (((C.filter (fun v => v.val < n₁)).card : ℝ)^2 / (n₁ : ℝ) +
              ((C.filter (fun v => n₁ ≤ v.val)).card : ℝ)^2 / (n₂ : ℝ) -
              (C.card : ℝ)^2 / ((n₁+n₂ : ℕ) : ℝ)) := by
      simp only [S₀, S₁, S₂, Finset.sum_div, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
    rw [interpolationClassDrift]
    simpa [Cset, S₀, S₁, S₂] using hscale.trans hsum
  · have hclasses : frozenClasses q G = ∅ := by
      simp [frozenClasses, frozenClass, Frozen, hcol]
    rw [h0, h1, h2, if_neg hcol]
    simp [interpolationClassDrift, hclasses]

theorem SA_I16bStatement_of_deps
    (h12b : SA_I12bStatement) (h14b : SA_I14bStatement)
    (h16a : SA_I16aStatement) : SA_I16bStatement := by
  intro q n₁ n₂ hq hn₁ hn₂ c hc θ hθ
  let μ : Fin 3 → ℝ := interpolationMeans n₁ n₂ c θ
  let rate : InterpolationMark n₁ n₂ → ℝ := markRate n₁ n₂ μ
  have hder := interpolationDerivative_addLoss h12b h16a q n₁ n₂ hq hn₁ hn₂ c θ hθ
  have hmean :
      -((n₁+n₂ : ℕ) : ℝ) *
          supportMean (fun T => addLoss q n₁ n₂ 0 (supportGraph T)) rate +
        (n₁ : ℝ) *
          supportMean (fun T => addLoss q n₁ n₂ 1 (supportGraph T)) rate +
        (n₂ : ℝ) *
          supportMean (fun T => addLoss q n₁ n₂ 2 (supportGraph T)) rate =
      supportMean (fun T =>
        -((n₁+n₂ : ℕ) : ℝ) * addLoss q n₁ n₂ 0 (supportGraph T) +
          (n₁ : ℝ) * addLoss q n₁ n₂ 1 (supportGraph T) +
          (n₂ : ℝ) * addLoss q n₁ n₂ 2 (supportGraph T)) rate := by
    simp only [supportMean, poissonSupportMean, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    ring
  have hdrift :
      supportMean (fun T =>
        -((n₁+n₂ : ℕ) : ℝ) * addLoss q n₁ n₂ 0 (supportGraph T) +
          (n₁ : ℝ) * addLoss q n₁ n₂ 1 (supportGraph T) +
          (n₂ : ℝ) * addLoss q n₁ n₂ 2 (supportGraph T)) rate =
        supportMean (fun T => interpolationClassDrift q n₁ n₂ (supportGraph T)) rate := by
    simp only [supportMean, poissonSupportMean]
    apply Finset.sum_congr rfl
    intro T hT
    exact congrArg (fun x : ℝ => poissonSupportWeight rate T * x)
      (lossCombo_eq_drift h14b q n₁ n₂ hq hn₁ hn₂ (supportGraph T))
  rw [hmean, hdrift] at hder
  simpa [driftMean, μ, rate] using hder

end ThLean.W.SA37

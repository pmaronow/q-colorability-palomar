import ThLean.BP.SA.Alternatives
import ThLean.W.SA50.Operators

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA50

open ThresholdFoundations ThLean.BP.SA

private def leftVertexEquiv (n₁ n₂ : ℕ) :
    Fin n₁ ≃ {v : Fin (n₁ + n₂) // v.val < n₁} where
  toFun i := ⟨leftVertex n₁ n₂ i, by simp [leftVertex]⟩
  invFun v := ⟨v.val, v.property⟩
  left_inv i := by ext; rfl
  right_inv v := by apply Subtype.ext; rfl

private def rightVertexEquiv (n₁ n₂ : ℕ) :
    Fin n₂ ≃ {v : Fin (n₁ + n₂) // n₁ ≤ v.val} where
  toFun i := ⟨rightVertex n₁ n₂ i, by simp [rightVertex]⟩
  invFun v := ⟨v.val - n₁, by have := v.val.isLt; omega⟩
  left_inv i := by
    apply Fin.ext
    simp [rightVertex]
  right_inv v := by
    apply Subtype.ext
    apply Fin.ext
    simp [rightVertex]
    omega

private def leftSet (n₁ n₂ : ℕ) : Finset (Fin (n₁ + n₂)) :=
  Finset.univ.filter (fun v => v.val < n₁)

private def rightSet (n₁ n₂ : ℕ) : Finset (Fin (n₁ + n₂)) :=
  Finset.univ.filter (fun v => n₁ ≤ v.val)

private theorem subtype_sum_eq_filter {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) :
    (∑ x : {x // p x}, f x.1) = ∑ x ∈ Finset.univ.filter p, f x := by
  classical
  rw [← Finset.sum_subtype_eq_sum_filter]
  simp

private theorem mean_fin_pair (n : ℕ) (f : Fin n × Fin n → ℝ) :
    uniformMean f =
      (∑ x : Fin n, ∑ y : Fin n, f (x, y)) / (n : ℝ) ^ 2 := by
  unfold uniformMean
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  ring

private def edgeDrop {V : Type*} (q : ℕ) (G : MGraph V) (e : Sym2 V) : ℝ :=
  indicator (Colorable q G) - indicator (Colorable q (addEdge G e))

private theorem edgeMean_indicator_drop {V E : Type*} [Fintype E] [Nonempty E]
    (edge : E → Sym2 V) (q : ℕ) (G : MGraph V) :
    edgeMean edge (fun H => indicator (Colorable q H)) G =
      indicator (Colorable q G) - uniformMean (fun e => edgeDrop q G (edge e)) := by
  unfold edgeMean edgeDrop
  calc
    uniformMean (fun e => indicator (Colorable q (addEdge G (edge e)))) =
        uniformMean (fun e => indicator (Colorable q G) -
          (indicator (Colorable q G) - indicator (Colorable q (addEdge G (edge e))))) :=
      mean_congr (fun _ => by ring)
    _ = uniformMean (fun _ : E => indicator (Colorable q G)) -
        uniformMean (fun e => indicator (Colorable q G) -
          indicator (Colorable q (addEdge G (edge e)))) := mean_sub _ _
    _ = _ := by rw [mean_const]

private theorem card_block_split {n₁ n₂ : ℕ} (C : Finset (Fin (n₁ + n₂))) :
    C.card = (C ∩ leftSet n₁ n₂).card + (C ∩ rightSet n₁ n₂).card := by
  classical
  let P : Fin (n₁ + n₂) → Prop := fun v => v.val < n₁
  have h := (Finset.card_filter_add_card_filter_not (s := C) P).symm
  simpa [leftSet, rightSet, P, Finset.inter_filter, Nat.not_lt] using h

private theorem class_loss_comparison (h15 : SA_I15Statement)
    {n₁ n₂ : ℕ} (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂)
    (Cs : Finset (Finset (Fin (n₁ + n₂)))) :
    (∑ C ∈ Cs, (((C ∩ leftSet n₁ n₂).card : ℝ) ^ 2)) / (n₁ : ℝ) +
      (∑ C ∈ Cs, (((C ∩ rightSet n₁ n₂).card : ℝ) ^ 2)) / (n₂ : ℝ) ≥
      (∑ C ∈ Cs, ((C.card : ℝ) ^ 2)) / ((n₁ + n₂ : ℕ) : ℝ) := by
  have hterm : ∀ C ∈ Cs,
      0 ≤ (((C ∩ leftSet n₁ n₂).card : ℝ) ^ 2) / (n₁ : ℝ) +
        (((C ∩ rightSet n₁ n₂).card : ℝ) ^ 2) / (n₂ : ℝ) -
        ((C.card : ℝ) ^ 2) / ((n₁ + n₂ : ℕ) : ℝ) := by
    intro C hC
    have hcard := card_block_split (n₁ := n₁) (n₂ := n₂) C
    have hcardR : (C.card : ℝ) =
        (C ∩ leftSet n₁ n₂).card + (C ∩ rightSet n₁ n₂).card := by
      exact_mod_cast hcard
    have h := (h15 (((C ∩ leftSet n₁ n₂).card : ℝ))
      (((C ∩ rightSet n₁ n₂).card : ℝ)) (n₁ : ℝ) (n₂ : ℝ)
      (by positivity) (by positivity)).2
    simpa [hcardR, Nat.cast_add] using h
  have hsum : 0 ≤ ∑ C ∈ Cs,
      ((((C ∩ leftSet n₁ n₂).card : ℝ) ^ 2) / (n₁ : ℝ) +
        (((C ∩ rightSet n₁ n₂).card : ℝ) ^ 2) / (n₂ : ℝ) -
        ((C.card : ℝ) ^ 2) / ((n₁ + n₂ : ℕ) : ℝ)) := by
    exact Finset.sum_nonneg (fun C hC => hterm C hC)
  have hparts := hsum
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hparts
  have hratio :
      (∑ C ∈ Cs, (((C ∩ leftSet n₁ n₂).card : ℝ) ^ 2)) / (n₁ : ℝ) +
        (∑ C ∈ Cs, (((C ∩ rightSet n₁ n₂).card : ℝ) ^ 2)) / (n₂ : ℝ) ≥
        (∑ C ∈ Cs, ((C.card : ℝ) ^ 2)) / ((n₁ + n₂ : ℕ) : ℝ) := by
    calc
      _ = (∑ C ∈ Cs, (((C ∩ leftSet n₁ n₂).card : ℝ) ^ 2) / (n₁ : ℝ)) +
          (∑ C ∈ Cs, (((C ∩ rightSet n₁ n₂).card : ℝ) ^ 2) / (n₂ : ℝ)) := by
            rw [Finset.sum_div, Finset.sum_div]
      _ ≥ ∑ C ∈ Cs, ((C.card : ℝ) ^ 2) / ((n₁ + n₂ : ℕ) : ℝ) := by
            linarith
      _ = _ := by rw [Finset.sum_div]
  exact hratio

private theorem global_drop_sum (h14b : SA_I14bStatement) {q n₁ n₂ : ℕ}
    (hq : 1 ≤ q) (G : MGraph (Fin (n₁ + n₂))) :
    (∑ x : Fin (n₁ + n₂), ∑ y : Fin (n₁ + n₂),
      edgeDrop q G (s(x, y))) =
      if Colorable q G then
        ∑ C ∈ frozenClasses q G, ((C.card : ℝ) ^ 2) else 0 := by
  have h := h14b (V := Fin (n₁ + n₂)) q G Finset.univ hq
  simpa only [edgeDrop, Finset.inter_univ] using h

private theorem left_drop_sum (h14b : SA_I14bStatement) {q n₁ n₂ : ℕ}
    (hq : 1 ≤ q) (G : MGraph (Fin (n₁ + n₂))) :
    (∑ xy : Fin n₁ × Fin n₁,
      edgeDrop q G (s(leftVertex n₁ n₂ xy.1, leftVertex n₁ n₂ xy.2))) =
      if Colorable q G then
        ∑ C ∈ frozenClasses q G, (((C ∩ leftSet n₁ n₂).card : ℝ) ^ 2) else 0 := by
  classical
  let P : Fin (n₁ + n₂) → Prop := fun v => v.val < n₁
  have hsum :
      (∑ xy : Fin n₁ × Fin n₁,
        edgeDrop q G (s(leftVertex n₁ n₂ xy.1, leftVertex n₁ n₂ xy.2))) =
      ∑ x ∈ leftSet n₁ n₂, ∑ y ∈ leftSet n₁ n₂, edgeDrop q G (s(x, y)) := by
    calc
      _ = ∑ xy : ({v : Fin (n₁ + n₂) // P v} ×
            {v : Fin (n₁ + n₂) // P v}), edgeDrop q G (s(xy.1.1, xy.2.1)) := by
          simpa [leftVertexEquiv, leftEdge, P] using
            (Equiv.prodCongr (leftVertexEquiv n₁ n₂) (leftVertexEquiv n₁ n₂)).sum_comp
              (fun xy => edgeDrop q G (s(xy.1.1, xy.2.1)))
      _ = ∑ x ∈ leftSet n₁ n₂, ∑ y ∈ leftSet n₁ n₂, edgeDrop q G (s(x, y)) := by
          simp only [Fintype.sum_prod_type]
          rw [subtype_sum_eq_filter (p := P)
            (f := fun x : Fin (n₁ + n₂) =>
              ∑ y : {v : Fin (n₁ + n₂) // P v}, edgeDrop q G (s(x, y.1)))]
          change (∑ x ∈ Finset.univ.filter P,
              ∑ y : {v : Fin (n₁ + n₂) // P v}, edgeDrop q G (s(x, y.1))) =
            ∑ x ∈ Finset.univ.filter P, ∑ y ∈ Finset.univ.filter P,
              edgeDrop q G (s(x, y))
          apply Finset.sum_congr rfl
          intro x hx
          rw [subtype_sum_eq_filter (p := P)
            (f := fun y => edgeDrop q G (s(x, y)))]
  rw [hsum]
  have h := h14b (V := Fin (n₁ + n₂)) q G (leftSet n₁ n₂) hq
  convert h using 1
  · rfl
  · by_cases hc : Colorable q G
    · simp [hc]
      apply Finset.sum_congr rfl
      intro C hC
      congr 1
      apply congrArg (fun S : Finset (Fin (n₁ + n₂)) => (S.card : ℝ))
      ext x
      simp
    · simp [hc]

private theorem right_drop_sum (h14b : SA_I14bStatement) {q n₁ n₂ : ℕ}
    (hq : 1 ≤ q) (G : MGraph (Fin (n₁ + n₂))) :
    (∑ xy : Fin n₂ × Fin n₂,
      edgeDrop q G (s(rightVertex n₁ n₂ xy.1, rightVertex n₁ n₂ xy.2))) =
      if Colorable q G then
        ∑ C ∈ frozenClasses q G, (((C ∩ rightSet n₁ n₂).card : ℝ) ^ 2) else 0 := by
  classical
  let P : Fin (n₁ + n₂) → Prop := fun v => n₁ ≤ v.val
  have hsum :
      (∑ xy : Fin n₂ × Fin n₂,
        edgeDrop q G (s(rightVertex n₁ n₂ xy.1, rightVertex n₁ n₂ xy.2))) =
      ∑ x ∈ rightSet n₁ n₂, ∑ y ∈ rightSet n₁ n₂, edgeDrop q G (s(x, y)) := by
    calc
      _ = ∑ xy : ({v : Fin (n₁ + n₂) // P v} ×
            {v : Fin (n₁ + n₂) // P v}), edgeDrop q G (s(xy.1.1, xy.2.1)) := by
          simpa [rightVertexEquiv, rightEdge, P] using
            (Equiv.prodCongr (rightVertexEquiv n₁ n₂) (rightVertexEquiv n₁ n₂)).sum_comp
              (fun xy => edgeDrop q G (s(xy.1.1, xy.2.1)))
      _ = ∑ x ∈ rightSet n₁ n₂, ∑ y ∈ rightSet n₁ n₂, edgeDrop q G (s(x, y)) := by
          simp only [Fintype.sum_prod_type]
          rw [subtype_sum_eq_filter (p := P)
            (f := fun x : Fin (n₁ + n₂) =>
              ∑ y : {v : Fin (n₁ + n₂) // P v}, edgeDrop q G (s(x, y.1)))]
          change (∑ x ∈ Finset.univ.filter P,
              ∑ y : {v : Fin (n₁ + n₂) // P v}, edgeDrop q G (s(x, y.1))) =
            ∑ x ∈ Finset.univ.filter P, ∑ y ∈ Finset.univ.filter P,
              edgeDrop q G (s(x, y))
          apply Finset.sum_congr rfl
          intro x hx
          rw [subtype_sum_eq_filter (p := P)
            (f := fun y => edgeDrop q G (s(x, y)))]
  rw [hsum]
  have h := h14b (V := Fin (n₁ + n₂)) q G (rightSet n₁ n₂) hq
  convert h using 1
  · rfl
  · by_cases hc : Colorable q G
    · simp [hc]
      apply Finset.sum_congr rfl
      intro C hC
      congr 1
      apply congrArg (fun S : Finset (Fin (n₁ + n₂)) => (S.card : ℝ))
      ext x
      simp
    · simp [hc]

private theorem step_indicator_le (h14b : SA_I14bStatement) (h15 : SA_I15Statement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂)
    (G : MGraph (Fin (n₁ + n₂))) :
    localStep n₁ n₂ (fun H => indicator (Colorable q H)) G ≤
      globalStep n₁ n₂ (fun H => indicator (Colorable q H)) G := by
  classical
  let N : ℝ := ((n₁ + n₂ : ℕ) : ℝ)
  let S₀ : ℝ := ∑ C ∈ frozenClasses q G, ((C.card : ℝ) ^ 2)
  let S₁ : ℝ := ∑ C ∈ frozenClasses q G,
    (((C ∩ leftSet n₁ n₂).card : ℝ) ^ 2)
  let S₂ : ℝ := ∑ C ∈ frozenClasses q G,
    (((C ∩ rightSet n₁ n₂).card : ℝ) ^ 2)
  have hn₁ : 0 < n₁ := by omega
  have hn₂ : 0 < n₂ := by omega
  have hN : 0 < N := by dsimp [N]; positivity
  have hNne : N ≠ 0 := ne_of_gt hN
  have hn₁ne : (n₁ : ℝ) ≠ 0 := by positivity
  have hn₂ne : (n₂ : ℝ) ≠ 0 := by positivity
  letI : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
  letI : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
  letI : Nonempty (Fin (n₁ + n₂)) := ⟨⟨0, by omega⟩⟩
  have hGdrop :
      uniformMean (fun xy : Fin (n₁ + n₂) × Fin (n₁ + n₂) =>
        edgeDrop q G (globalEdge n₁ n₂ xy)) =
      (if Colorable q G then S₀ else 0) / N ^ 2 := by
    rw [mean_fin_pair]
    simpa [globalEdge, S₀, N] using
      congrArg (fun x : ℝ => x / N ^ 2) (global_drop_sum h14b hq G)
  have hLdrop :
      uniformMean (fun xy : Fin n₁ × Fin n₁ =>
        edgeDrop q G (leftEdge n₁ n₂ xy)) =
      (if Colorable q G then S₁ else 0) / (n₁ : ℝ) ^ 2 := by
    rw [mean_fin_pair]
    have hs := left_drop_sum h14b hq G
    rw [Fintype.sum_prod_type] at hs
    simpa [leftEdge, S₁] using
      congrArg (fun x : ℝ => x / (n₁ : ℝ) ^ 2) hs
  have hRdrop :
      uniformMean (fun xy : Fin n₂ × Fin n₂ =>
        edgeDrop q G (rightEdge n₁ n₂ xy)) =
      (if Colorable q G then S₂ else 0) / (n₂ : ℝ) ^ 2 := by
    rw [mean_fin_pair]
    have hs := right_drop_sum h14b hq G
    rw [Fintype.sum_prod_type] at hs
    simpa [rightEdge, S₂] using
      congrArg (fun x : ℝ => x / (n₂ : ℝ) ^ 2) hs
  have hGval :
      globalStep n₁ n₂ (fun H => indicator (Colorable q H)) G =
        indicator (Colorable q G) - (if Colorable q G then S₀ else 0) / N ^ 2 := by
    rw [globalStep_eq_edgeMean, edgeMean_indicator_drop (globalEdge n₁ n₂) q G,
      hGdrop]
  have hLval :
      localStep n₁ n₂ (fun H => indicator (Colorable q H)) G =
        (n₁ : ℝ) / N * (indicator (Colorable q G) -
          (if Colorable q G then S₁ else 0) / (n₁ : ℝ) ^ 2) +
        (n₂ : ℝ) / N * (indicator (Colorable q G) -
          (if Colorable q G then S₂ else 0) / (n₂ : ℝ) ^ 2) := by
    rw [localStep_eq_edgeMeans]
    change (n₁ : ℝ) / N *
        edgeMean (leftEdge n₁ n₂) (fun H => indicator (Colorable q H)) G +
      (n₂ : ℝ) / N *
        edgeMean (rightEdge n₁ n₂) (fun H => indicator (Colorable q H)) G = _
    rw [edgeMean_indicator_drop (leftEdge n₁ n₂) q G,
      edgeMean_indicator_drop (rightEdge n₁ n₂) q G,
      hLdrop, hRdrop]
  have hcoef : (n₁ : ℝ) / N + (n₂ : ℝ) / N = 1 := by
    dsimp [N]
    field_simp [ne_of_gt (show (0 : ℝ) < ((n₁ + n₂ : ℕ) : ℝ) by positivity)]
    norm_num [Nat.cast_add]
  have hclass := class_loss_comparison h15 h₁ h₂ (frozenClasses q G)
  have hratio : S₁ / (n₁ : ℝ) + S₂ / (n₂ : ℝ) ≥ S₀ / N := by
    simpa [S₀, S₁, S₂, N] using hclass
  have hscaled : S₀ / N ^ 2 ≤
      (n₁ : ℝ) / N * (S₁ / (n₁ : ℝ) ^ 2) +
        (n₂ : ℝ) / N * (S₂ / (n₂ : ℝ) ^ 2) := by
    have hdiv := div_le_div_of_nonneg_right hratio (le_of_lt hN)
    have hleft : (S₀ / N) / N = S₀ / N ^ 2 := by
      field_simp [hNne]
    have hright : (S₁ / (n₁ : ℝ) + S₂ / (n₂ : ℝ)) / N =
        (n₁ : ℝ) / N * (S₁ / (n₁ : ℝ) ^ 2) +
          (n₂ : ℝ) / N * (S₂ / (n₂ : ℝ) ^ 2) := by
      field_simp [hNne, hn₁ne, hn₂ne]
    calc
      _ = (S₀ / N) / N := hleft.symm
      _ ≤ (S₁ / (n₁ : ℝ) + S₂ / (n₂ : ℝ)) / N := hdiv
      _ = _ := hright
  by_cases hc : Colorable q G
  · have hg : globalStep n₁ n₂ (fun H => indicator (Colorable q H)) G =
        1 - S₀ / N ^ 2 := by
      simpa [hc, indicator] using hGval
    have hl : localStep n₁ n₂ (fun H => indicator (Colorable q H)) G =
        (n₁ : ℝ) / N * (1 - S₁ / (n₁ : ℝ) ^ 2) +
          (n₂ : ℝ) / N * (1 - S₂ / (n₂ : ℝ) ^ 2) := by
      simpa [hc, indicator] using hLval
    rw [hl, hg]
    linarith
  · have hg : globalStep n₁ n₂ (fun H => indicator (Colorable q H)) G = 0 := by
      simpa [hc, indicator] using hGval
    have hl : localStep n₁ n₂ (fun H => indicator (Colorable q H)) G = 0 := by
      simpa [hc, indicator] using hLval
    rw [hl, hg]

theorem SA_R70aStatement_of_deps (h14b : SA_I14bStatement)
    (h15 : SA_I15Statement) : SA_R70aStatement := by
  intro q n₁ n₂ hq h₁ h₂ m G
  let f : MGraph (Fin (n₁ + n₂)) → ℝ := fun H => indicator (Colorable q H)
  have hstep : localStep n₁ n₂ f ≤ globalStep n₁ n₂ f := by
    intro H
    exact step_indicator_le h14b h15 q n₁ n₂ hq h₁ h₂ H
  have hiter := iterate_compare_of_commute
    (globalStep n₁ n₂) (localStep n₁ n₂)
    (globalStep_mono n₁ n₂) (localStep_mono n₁ n₂ h₁ h₂)
    (global_local_commute n₁ n₂) hstep m
  exact hiter G

end ThLean.W.SA50

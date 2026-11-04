module

public import ThLean.BP.SA.Interpolation

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA38
open ThresholdFoundations

private theorem square_drift_nonneg (a b r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    0 ≤ a ^ 2 / r + b ^ 2 / s - (a + b) ^ 2 / (r + s) := by
  have hrs : 0 < r + s := add_pos hr hs
  have hid : a ^ 2 / r + b ^ 2 / s - (a + b) ^ 2 / (r + s) =
      (s * a - r * b) ^ 2 / (r * s * (r + s)) := by
    field_simp
    ring
  rw [hid]
  exact div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (mul_pos hr hs) hrs))

private theorem frozen_class_card_split {n₁ n₂ : ℕ}
    (C : Finset (Fin (n₁ + n₂))) :
    C.card = (C.filter (fun v => v.val < n₁)).card +
      (C.filter (fun v => n₁ ≤ v.val)).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := C) (p := fun v : Fin (n₁ + n₂) => v.val < n₁)
  simpa [Nat.not_lt] using h.symm

private theorem interpolation_drift_nonneg (q n₁ n₂ : ℕ)
    (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (G : MGraph (Fin (n₁ + n₂))) : 0 ≤ ThLean.BP.SA.drift q n₁ n₂ G := by
  unfold ThLean.BP.SA.drift ThresholdFoundations.interpolationClassDrift
  apply Finset.sum_nonneg
  intro C _
  let a : ℝ := (C.filter (fun v : Fin (n₁ + n₂) => v.val < n₁)).card
  let b : ℝ := (C.filter (fun v : Fin (n₁ + n₂) => n₁ ≤ v.val)).card
  have hsplit := frozen_class_card_split (n₁ := n₁) (n₂ := n₂) C
  have hsplitR : (C.card : ℝ) = a + b := by
    dsimp [a, b]
    exact_mod_cast hsplit
  have hr : 0 < (n₁ : ℝ) := by
    exact_mod_cast (show 0 < n₁ by omega)
  have hs : 0 < (n₂ : ℝ) := by
    exact_mod_cast (show 0 < n₂ by omega)
  change 0 ≤ a ^ 2 / (n₁ : ℝ) + b ^ 2 / (n₂ : ℝ) -
    (C.card : ℝ) ^ 2 / ((n₁ + n₂ : ℕ) : ℝ)
  rw [hsplitR, Nat.cast_add]
  exact square_drift_nonneg a b (n₁ : ℝ) (n₂ : ℝ) hr hs

private theorem poisson_support_weight_nonneg {D : Type} [Fintype D]
    (rate : D → ℝ) (T : Finset D) (hrate : ∀ e, 0 ≤ rate e) :
    0 ≤ ThLean.BP.SA.supportWeight rate T := by
  unfold ThLean.BP.SA.supportWeight ThresholdFoundations.poissonSupportWeight
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro e he
    have hexp : Real.exp (-rate e) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith [hrate e]
    linarith
  · apply Finset.prod_nonneg
    intro e he
    exact le_of_lt (Real.exp_pos _)

private theorem interpolation_mark_rates_nonneg {n₁ n₂ : ℕ}
    (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) {c θ : ℝ}
    (_hc : 0 ≤ c) (hθ : θ ∈ Set.Icc 0 c) :
    ∀ e : ThLean.BP.SA.TaggedMark n₁ n₂,
      0 ≤ ThLean.BP.SA.markRate n₁ n₂
        (interpolationMeans n₁ n₂ c θ) e := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθc : θ ≤ c := hθ.2
  have hN : 0 < n₁ + n₂ := by omega
  have hμ : ∀ i : Fin 3, 0 ≤ interpolationMeans n₁ n₂ c θ i := by
    intro i
    fin_cases i <;> simp [ThresholdFoundations.interpolationMeans] <;> positivity
  intro e
  cases e with
  | inl xy =>
      simp [ThLean.BP.SA.markRate, ThresholdFoundations.interpolationMarkRate]
      exact div_nonneg (hμ 0) (sq_nonneg _)
  | inr rest =>
      cases rest with
      | inl xy =>
          simp [ThLean.BP.SA.markRate, ThresholdFoundations.interpolationMarkRate]
          exact div_nonneg (hμ 1) (sq_nonneg _)
      | inr xy =>
          simp [ThLean.BP.SA.markRate, ThresholdFoundations.interpolationMarkRate]
          exact div_nonneg (hμ 2) (sq_nonneg _)

/-- The classwise and expected interpolation drifts are nonnegative. -/
theorem SA_I16cStatement_holds : ThLean.BP.SA.SA_I16cStatement := by
  intro q n₁ n₂ hnq hn₁ hn₂
  constructor
  · intro G
    exact interpolation_drift_nonneg q n₁ n₂ hn₁ hn₂ G
  · intro c hc θ hθ
    unfold ThLean.BP.SA.driftMean ThLean.BP.SA.supportMean
    apply Finset.sum_nonneg
    intro T hT
    apply mul_nonneg
    · exact poisson_support_weight_nonneg
        (ThLean.BP.SA.markRate n₁ n₂ (interpolationMeans n₁ n₂ c θ)) T
        (interpolation_mark_rates_nonneg hn₁ hn₂ hc hθ)
    · exact interpolation_drift_nonneg q n₁ n₂ hn₁ hn₂
        (ThLean.BP.SA.supportGraph (n₁ := n₁) (n₂ := n₂) T)

end ThLean.W.SA38

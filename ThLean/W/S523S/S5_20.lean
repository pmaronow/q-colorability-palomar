import ThLean.W.S523S.Aggregation
import ThLean.W.S523S.Measurability

noncomputable section
open MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S523S
open ThresholdFoundations ThLean.BP.S5

private theorem abs_add_bound {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a + b| ≤ 2 := (abs_add_le a b).trans (by linarith)

theorem three_means_bound
    {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    {r : I → ℝ} {t : J → ℝ} {u : K → ℝ}
    (hr : ∀ i, 0 ≤ r i) (ht : ∀ j, 0 ≤ t j) (hu : ∀ k, 0 ≤ u k)
    (f : (I → ℕ) → (J → ℕ) → (K → ℕ) → ℝ)
    (a : (J → ℕ) → ℝ) (g : (I → ℕ) → (K → ℕ) → ℝ)
    (hf : ∀ x y z, |f x y z| ≤ 1) (ha : ∀ y, |a y| ≤ 1)
    (hg : ∀ x z, |g x z| ≤ 1) (hle : ∀ x y z, f x y z ≤ a y + g x z) :
    mean r (fun x => mean t (fun y => mean u (f x y))) ≤
      mean t a + mean r (fun x => mean u (g x)) := by
  have h₁ (x) (y) : mean u (f x y) ≤ a y + mean u (g x) := by
    calc
      _ ≤ mean u (fun z => a y + g x z) := mean_mono hu
        ⟨1, hf x y⟩ ⟨2, fun z => abs_add_bound (ha y) (hg x z)⟩ (hle x y)
      _ = _ := by rw [mean_add hu ⟨|a y|, fun _ => le_rfl⟩ ⟨1, hg x⟩, mean_const hu]
  have h₂ (x) : mean t (fun y => mean u (f x y)) ≤ mean t a + mean u (g x) := by
    calc
      _ ≤ mean t (fun y => a y + mean u (g x)) := mean_mono ht
        ⟨1, fun y => mean_abs_le hu (hf x y)⟩
        ⟨2, fun y => abs_add_bound (ha y) (mean_abs_le hu (hg x))⟩ (h₁ x)
      _ = _ := by
        rw [mean_add ht ⟨1, ha⟩ ⟨|mean u (g x)|, fun _ => le_rfl⟩, mean_const ht]
  calc
    _ ≤ mean r (fun x => mean t a + mean u (g x)) := mean_mono hr
      ⟨1, fun x => mean_abs_le ht (fun y => mean_abs_le hu (hf x y))⟩
      ⟨2, fun x => abs_add_bound (mean_abs_le ht ha) (mean_abs_le hu (hg x))⟩ h₂
    _ = _ := by
      rw [mean_add hr ⟨|mean t a|, fun _ => le_rfl⟩
        ⟨1, fun x => mean_abs_le hu (hg x)⟩, mean_const hr]

theorem fixedIdentification_bound
    (h07 : S5_07Statement) (h09a : S5_09AStatement) (h09c : S5_09CStatement)
    (q N : ℕ) (hN : 3 ≤ N) (Z : Finset (Fin N)) (hZ : Z.Nonempty)
    (hNZ : 2 ≤ N - Z.card) (s : ℝ) (hs : 0 ≤ s) :
    poissonGraphMean s (fun G : MGraph (Fin N) =>
      indicator (Colorable q G ∧ ¬ Colorable q (identify G Z))) ≤
      lowEdgeRate N * (Z.card.choose 2 : ℝ) * s +
        addedFailure (V := {v : Fin N // v ∉ Z}) q
          (lowEdgeRate N * s) (Z.card * neighborMean N Z.card s) := by
  classical
  -- Save the original enumeration without making it a local instance.
  let nativeOutside : ULift.{0, 0} (Fintype {v : Fin N // v ∉ Z}) := ⟨inferInstance⟩
  -- Match the equality instance in the generic splitting contracts.
  let : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a = b)
  let A := {v : Fin N // v ∈ Z}
  let V := {v : Fin N // v ∉ Z}
  have hA : Fintype.card A = Z.card := Fintype.card_coe Z
  have hV : Fintype.card V = N - Z.card := by
    dsimp [V]
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let r := lowEdgeRate N * s
  have hr : 0 ≤ r := by dsimp [r, lowEdgeRate]; positivity
  have hz : 0 ≤ (Fintype.card A : ℝ) * Fintype.card V * r := by positivity
  have hrate : s / ((Fintype.card (Fin N)).choose 2 : ℝ) = r := by
    simp [r, lowEdgeRate, div_eq_mul_inv, mul_comm]
  have hparam : (Fintype.card A : ℝ) * Fintype.card V * r =
      Z.card * neighborMean N Z.card s := by
    rw [hA, hV]
    dsimp [r, neighborMean]
    ring
  let F := fun (B : MGraph V) (R : MGraph A) (c : A × V → ℕ) =>
    indicator (Colorable q (mapGraph Subtype.val B + mapGraph Subtype.val R + crossGraph Z c) ∧
      ¬ Colorable q (identify (mapGraph Subtype.val B + mapGraph Subtype.val R + crossGraph Z c) Z))
  let Q := fun (B : MGraph V) (c : A × V → ℕ) =>
    indicator (Colorable q B ∧
      ¬ Colorable q (addRoot B (countsList (fun v => ∑ a, c (a, v)))))
  have hsplit := h09a (Fin N) (by simpa using hN) Z hZ (by simpa using hNZ) s hs
    (fun G => indicator (Colorable q G ∧ ¬ Colorable q (identify G Z)))
    ⟨1, fun _ => (indicator_bounds _).2⟩
  rw [hrate] at hsplit
  simp only [countMean_eq_mean] at hsplit
  have hsplit' : poissonGraphMean s (fun G : MGraph (Fin N) =>
      indicator (Colorable q G ∧ ¬Colorable q (identify G Z))) =
      mean (perPairRate r) (fun B : MGraph V =>
        mean (perPairRate r) (fun R : MGraph A => mean (fun _ : A × V => r) (F B R))) := by
    dsimp only [mean, mass, F, crossGraph] at hsplit ⊢
    exact hsplit
  rw [hsplit']
  have hbound := three_means_bound
    (perPairRate_nonneg (V := V) hr) (perPairRate_nonneg (V := A) hr)
    (fun _ : A × V => hr) F (fun R : MGraph A => indicator (R ≠ 0)) Q
    (fun _ _ _ => (indicator_bounds _).2) (fun _ => (indicator_bounds _).2)
    (fun _ _ => (indicator_bounds _).2) (fun B R c => split_event_bound h07 q Z hZ B R c)
  refine hbound.trans ?_
  have hcross (B : MGraph V) : mean (fun _ : A × V => r) (Q B) =
      poissonMixture (Fintype.card A * Fintype.card V * r) (blocking q B) :=
    crossing_blocking h09c A V q B r hr
  simp_rw [hcross]
  change countMean r (fun R : MGraph A => indicator (R ≠ 0)) +
    countMean r (fun B : MGraph V =>
      poissonMixture (Fintype.card A * Fintype.card V * r) (blocking q B)) ≤ _
  rw [addedFailure_comm q hr hz, hparam]
  have hint := countMean_nonzero_le (V := A) hr
  rw [hA] at hint
  have hc : ((Z.card.choose 2 : ℕ) : ℝ) * r = lowEdgeRate N * (Z.card.choose 2 : ℝ) * s := by
    dsimp [r]
    ring
  rw [hc] at hint
  have hlast : addedFailure (V := V) q r (Z.card * neighborMean N Z.card s) ≤
      @addedFailure V nativeOutside.down q r (Z.card * neighborMean N Z.card s) := by
    have he : (inferInstance : Fintype V) = nativeOutside.down := Subsingleton.elim _ _
    exact le_of_eq (congrArg (fun i : Fintype V =>
      @addedFailure V i q r (Z.card * neighborMean N Z.card s)) he)
  exact add_le_add hint hlast

/-- The original leaf, with only its quotient and two splitting leaves as premises. -/
theorem S5_20Statement_of_deps
    (h07 : ThLean.BP.S5.S5_07Statement)
    (h09a : ThLean.BP.S5.S5_09AStatement)
    (h09c : ThLean.BP.S5.S5_09CStatement) : ThLean.BP.S5.S5_20Statement := by
  intro q N _ hN Z hZ hNZ
  exact ⟨fixedIdentification_bound h07 h09a h09c q N hN Z hZ hNZ,
    fixedIdentification_measurable q N Z⟩

example (h07 : ThLean.BP.S5.S5_07Statement) (h09a : ThLean.BP.S5.S5_09AStatement)
    (h09c : ThLean.BP.S5.S5_09CStatement) : ThLean.BP.S5.S5_20Statement :=
  S5_20Statement_of_deps h07 h09a h09c

end ThLean.W.S523S

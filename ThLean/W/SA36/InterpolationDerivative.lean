import ThLean.BP.SA.Interpolation

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA36
open ThresholdFoundations ThLean.BP.SA

private theorem supportMean_contDiff {D : Type} [Fintype D]
    (F : Finset D → ℝ) :
    ContDiff ℝ ⊤ (fun r : D → ℝ => supportMean F r) := by
  unfold supportMean poissonSupportMean poissonSupportWeight
  fun_prop

private theorem supportMean_affine_deriv_of_I12a
    (h12 : SA_I12aStatement) {D : Type} [Fintype D] [DecidableEq D]
    (F : Finset D → ℝ) (α β : D → ℝ) (t : ℝ) :
    HasDerivAt (fun t => supportMean F (fun e => α e * t + β e))
      (∑ e, α e * supportMean (fun T => F (insert e T) - F T)
        (fun e => α e * t + β e)) t := by
  let S : (D → ℝ) → ℝ := fun r => supportMean F r
  have hS : ContDiff ℝ ⊤ S := supportMean_contDiff F
  let r : D → ℝ := fun e => α e * t + β e
  have hSr : HasFDerivAt S (fderiv ℝ S r) r :=
    ((hS.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hcurve : HasDerivAt (fun x : ℝ => fun e => α e * x + β e) α t := by
    apply hasDerivAt_pi.mpr
    intro e
    simpa using ((hasDerivAt_id t).const_mul (α e)).add_const (β e)
  have hcoord (e : D) :
      fderiv ℝ S r (Pi.single e (1 : ℝ)) =
        supportMean (fun T => F (insert e T) - F T) r := by
    have hSrE : HasFDerivAt S (fderiv ℝ S r) (Function.update r e (r e)) := by
      simpa using hSr
    have hcomp := HasFDerivAt.comp_hasDerivAt
      (l := S) (f := Function.update r e) (x := r e) hSrE
      (hasDerivAt_update r e (r e))
    have h12e := h12 D F r e
    have hEq := hcomp.unique h12e
    simpa [S, Function.comp_def] using hEq
  have hdecomp : α = ∑ e : D, Pi.single e (α e) := by
    funext i
    simp
  have hsum : (fderiv ℝ S r) α =
      ∑ e : D, α e * supportMean (fun T => F (insert e T) - F T) r := by
    rw [hdecomp, map_sum]
    refine Finset.sum_congr rfl ?_
    intro e he
    rw [show Pi.single e (α e) = α e • Pi.single e (1 : ℝ) by
      ext i
      simp [Pi.single_apply]]
    rw [map_smul, hcoord]
    simp [smul_eq_mul]
  have hcomp := HasFDerivAt.comp_hasDerivAt
    (l := S) (f := fun x : ℝ => fun e => α e * x + β e) (x := t) hSr hcurve
  simpa [S, Function.comp_def, r, hsum] using hcomp

private theorem edgeSupport_supportGraph_insert {n₁ n₂ : ℕ}
    (T : Finset (TaggedMark n₁ n₂)) (m : TaggedMark n₁ n₂) :
    edgeSupport (supportGraph (insert m T)) =
      edgeSupport (supportGraph T) ∪ {markEdge m} := by
  ext e
  simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    ThLean.BP.SA.supportGraph, ThresholdFoundations.supportGraph, Finset.card_pos,
    Finset.mem_union, Finset.mem_singleton]
  rw [Finset.filter_insert]
  by_cases h : interpolationMarkEdge m = e
  · simp [markEdge, h]
  · rw [if_neg h]
    have h' : e ≠ markEdge m := by
      intro he
      exact h (by simpa [markEdge] using he.symm)
    simp [h']

private theorem edgeSupport_addEdge_union {V : Type} [Fintype V]
    (G : MGraph V) (e₀ : Sym2 V) :
    edgeSupport (addEdge G e₀) = edgeSupport G ∪ {e₀} := by
  ext e
  simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton]
  by_cases h : e = e₀
  · subst e
    simp [addEdge]
  · simp [addEdge, h]

private theorem colorable_congr_edgeSupport {V : Type} [Fintype V]
    (h10 : SA_I10Statement) (q : ℕ) (hq : 1 ≤ q) (G G' : MGraph V)
    (hs : edgeSupport G = edgeSupport G') : Colorable q G ↔ Colorable q G' := by
  have heq := h10 V q hq |>.1 G G' hs
  constructor
  · rintro ⟨σ, hσ⟩
    have hm : σ ∈ colorings q G := by simp [colorings, hσ]
    rw [heq] at hm
    exact ⟨σ, (Finset.mem_filter.mp hm).2⟩
  · rintro ⟨σ, hσ⟩
    have hm : σ ∈ colorings q G' := by simp [colorings, hσ]
    rw [← heq] at hm
    exact ⟨σ, (Finset.mem_filter.mp hm).2⟩

private theorem indicator_addEdge_delta {V : Type} [Fintype V]
    (h10 : SA_I10Statement) (q : ℕ) (hq : 1 ≤ q) (G : MGraph V) (x y : V) :
    indicator (Colorable q (addEdge G s(x, y))) - indicator (Colorable q G) =
      -indicator (Colorable q G ∧ ¬ Colorable q (addEdge G s(x, y))) := by
  have hmono : Colorable q (addEdge G s(x, y)) → Colorable q G := by
    rintro ⟨σ, hσ⟩
    exact ⟨σ, ((h10 V q hq).2.2 G x y σ).mp hσ |>.1⟩
  by_cases hG : Colorable q G
  · by_cases hA : Colorable q (addEdge G s(x, y)) <;> simp [indicator, hG, hA]
  · by_cases hA : Colorable q (addEdge G s(x, y))
    · exact (hG (hmono hA)).elim
    · simp [indicator, hG, hA]

private theorem supportMean_sum {D A : Type} [Fintype D] [Fintype A]
    [DecidableEq D] (rates : D → ℝ) (g : A → Finset D → ℝ) :
    (∑ a, supportMean (g a) rates) = supportMean (fun T => ∑ a, g a T) rates := by
  simp only [supportMean, ThresholdFoundations.poissonSupportMean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mul_sum]

private theorem sum_insert_increment_eq_addLoss {n₁ n₂ : ℕ}
    (h10 : SA_I10Statement) (q : ℕ) (hq : 1 ≤ q)
    (A : Type) [Fintype A] [DecidableEq A] (hA : Fintype.card A ≠ 0)
    (rates : TaggedMark n₁ n₂ → ℝ) (tag : A → TaggedMark n₁ n₂)
    (x y : A → Fin (n₁ + n₂)) (j : Fin 3)
    (hedge : ∀ a, markEdge (tag a) = s(x a, y a))
    (hLoss : ∀ T, addLoss q n₁ n₂ j (supportGraph T) =
      uniformMean (fun a => indicator
        (Colorable q (supportGraph T) ∧ ¬ Colorable q
          (addEdge (supportGraph T) s(x a, y a))))) :
    (∑ a, supportMean (fun T =>
      indicator (Colorable q (supportGraph (insert (tag a) T))) -
        indicator (Colorable q (supportGraph T))) rates) =
      -(Fintype.card A : ℝ) *
        supportMean (fun T => addLoss q n₁ n₂ j (supportGraph T)) rates := by
  rw [supportMean_sum]
  have hpoint (T : Finset (TaggedMark n₁ n₂)) :
      (∑ a, (indicator (Colorable q (supportGraph (insert (tag a) T))) -
        indicator (Colorable q (supportGraph T)))) =
      -(Fintype.card A : ℝ) * addLoss q n₁ n₂ j (supportGraph T) := by
    calc
      _ = ∑ a, -indicator (Colorable q (supportGraph T) ∧ ¬ Colorable q
            (addEdge (supportGraph T) s(x a, y a))) := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        have hs : edgeSupport (supportGraph (insert (tag a) T)) =
            edgeSupport (addEdge (supportGraph T) s(x a, y a)) := by
          rw [edgeSupport_supportGraph_insert, edgeSupport_addEdge_union, hedge]
          ext z
          simp
        have hc := colorable_congr_edgeSupport h10 q hq (supportGraph (insert (tag a) T))
          (addEdge (supportGraph T) s(x a, y a)) hs
        rw [hc]
        exact indicator_addEdge_delta h10 q hq (supportGraph T) (x a) (y a)
      _ = -(∑ a, indicator (Colorable q (supportGraph T) ∧ ¬ Colorable q
            (addEdge (supportGraph T) s(x a, y a)))) := by simp
      _ = -(Fintype.card A : ℝ) * addLoss q n₁ n₂ j (supportGraph T) := by
        rw [hLoss T]
        have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast hA
        simp only [uniformMean]
        field_simp [hcard]
  have hf : (fun T => ∑ a, (indicator (Colorable q (supportGraph (insert (tag a) T))) -
      indicator (Colorable q (supportGraph T)))) =
      (fun T => -(Fintype.card A : ℝ) * addLoss q n₁ n₂ j (supportGraph T)) := by
    funext T
    exact hpoint T
  rw [hf]
  simp [supportMean, ThresholdFoundations.poissonSupportMean, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

theorem SA_I16aStatement_of_deps (h10 : SA_I10Statement)
    (h12 : SA_I12aStatement) : SA_I16aStatement := by
  intro q n₁ n₂ hq h₁ h₂ μ hμ j
  fin_cases j
  · let N : ℝ := ((n₁ + n₂ : ℕ) : ℝ)
    let d : ℝ := N ^ 2
    let F : Finset (TaggedMark n₁ n₂) → ℝ := fun T =>
      indicator (Colorable q (supportGraph T))
    let r : TaggedMark n₁ n₂ → ℝ := markRate n₁ n₂ μ
    let α : TaggedMark n₁ n₂ → ℝ := fun e =>
      match e with
      | .inl _ => 1 / d
      | .inr _ => 0
    let β : TaggedMark n₁ n₂ → ℝ := fun e => r e - α e * μ 0
    have hpath (t : ℝ) : markRate n₁ n₂ (Function.update μ 0 t) =
        fun e => α e * t + β e := by
      funext e
      cases e with
      | inl xy => simp [markRate, ThresholdFoundations.interpolationMarkRate, α, β, r, d, N]; ring
      | inr z => cases z with
        | inl xy => simp [markRate, ThresholdFoundations.interpolationMarkRate, α, β, r]
        | inr xy => simp [markRate, ThresholdFoundations.interpolationMarkRate, α, β, r]
    have hA : Fintype.card (Fin (n₁+n₂) × Fin (n₁+n₂)) ≠ 0 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
    have hd : d ≠ 0 := by
      dsimp [d, N]
      positivity
    have hcard : (Fintype.card (Fin (n₁+n₂) × Fin (n₁+n₂)) : ℝ) = d := by
      simp [d, N, Fintype.card_prod]
      ring
    have hsumα :
        (∑ e : TaggedMark n₁ n₂,
          α e * supportMean (fun T => F (insert e T) - F T) r) =
          (1 / d) * ∑ xy : Fin (n₁+n₂) × Fin (n₁+n₂),
            supportMean (fun T => F (insert (.inl xy) T) - F T) r := by
      simp only [Fintype.sum_sum_type, α, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
      rw [← Finset.mul_sum]
    have hloss :
        (∑ xy : Fin (n₁+n₂) × Fin (n₁+n₂),
          supportMean (fun T => F (insert (.inl xy) T) - F T) r) =
          -(Fintype.card (Fin (n₁+n₂) × Fin (n₁+n₂)) : ℝ) *
            supportMean (fun T => addLoss q n₁ n₂ 0 (supportGraph T)) r := by
      simpa [F] using sum_insert_increment_eq_addLoss h10 q hq
        (Fin (n₁+n₂) × Fin (n₁+n₂)) hA
        r Sum.inl Prod.fst Prod.snd 0 (by intro a; rfl) (by intro T; rfl)
    have hvalue :
        (∑ e : TaggedMark n₁ n₂,
          α e * supportMean (fun T => F (insert e T) - F T) r) =
          -supportMean (fun T => addLoss q n₁ n₂ 0 (supportGraph T)) r := by
      rw [hsumα, hloss, hcard]
      field_simp [hd]
    have hderiv := supportMean_affine_deriv_of_I12a h12 F α β (μ 0)
    have hbase : r = (fun e => α e * μ 0 + β e) := by
      simpa [r, Function.update_self] using hpath (μ 0)
    rw [← hbase] at hderiv
    rw [hvalue] at hderiv
    have hfun : (fun t => finiteChiBar q n₁ n₂ (Function.update μ 0 t)) =
        (fun t => supportMean F (fun e => α e * t + β e)) := by
      funext t
      change supportMean F (markRate n₁ n₂ (Function.update μ 0 t)) = _
      rw [hpath t]
    rw [← hfun] at hderiv
    simpa [F, r] using hderiv
  · let N : ℝ := (n₁ : ℝ)
    let d : ℝ := N ^ 2
    let F : Finset (TaggedMark n₁ n₂) → ℝ := fun T =>
      indicator (Colorable q (supportGraph T))
    let r : TaggedMark n₁ n₂ → ℝ := markRate n₁ n₂ μ
    let α : TaggedMark n₁ n₂ → ℝ := fun e =>
      match e with
      | .inl _ => 0
      | .inr (.inl _) => 1 / d
      | .inr (.inr _) => 0
    let β : TaggedMark n₁ n₂ → ℝ := fun e => r e - α e * μ 1
    have hpath (t : ℝ) : markRate n₁ n₂ (Function.update μ 1 t) =
        fun e => α e * t + β e := by
      funext e
      cases e with
      | inl xy => simp [markRate, ThresholdFoundations.interpolationMarkRate, α, β, r]
      | inr z => cases z with
        | inl xy => simp [markRate, ThresholdFoundations.interpolationMarkRate, α, β, r, d, N]; ring
        | inr xy => simp [markRate, ThresholdFoundations.interpolationMarkRate, α, β, r]
    have hA : Fintype.card (Fin n₁ × Fin n₁) ≠ 0 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
    have hd : d ≠ 0 := by dsimp [d, N]; positivity
    have hcard : (Fintype.card (Fin n₁ × Fin n₁) : ℝ) = d := by
      simp [d, N, Fintype.card_prod]
      ring
    have hsumα :
        (∑ e : TaggedMark n₁ n₂,
          α e * supportMean (fun T => F (insert e T) - F T) r) =
          (1 / d) * ∑ xy : Fin n₁ × Fin n₁,
            supportMean (fun T => F (insert (.inr (.inl xy)) T) - F T) r := by
      simp only [Fintype.sum_sum_type, α, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
      rw [← Finset.mul_sum]
    have hloss :
        (∑ xy : Fin n₁ × Fin n₁,
          supportMean (fun T => F (insert (.inr (.inl xy)) T) - F T) r) =
          -(Fintype.card (Fin n₁ × Fin n₁) : ℝ) *
            supportMean (fun T => addLoss q n₁ n₂ 1 (supportGraph T)) r := by
      simpa [F] using sum_insert_increment_eq_addLoss h10 q hq
        (Fin n₁ × Fin n₁) hA r
        (fun xy => Sum.inr (Sum.inl xy))
        (fun xy => leftVertex n₁ n₂ xy.1) (fun xy => leftVertex n₁ n₂ xy.2)
        1 (by intro a; rfl) (by intro T; rfl)
    have hvalue :
        (∑ e : TaggedMark n₁ n₂,
          α e * supportMean (fun T => F (insert e T) - F T) r) =
          -supportMean (fun T => addLoss q n₁ n₂ 1 (supportGraph T)) r := by
      rw [hsumα, hloss, hcard]
      field_simp [hd]
    have hderiv := supportMean_affine_deriv_of_I12a h12 F α β (μ 1)
    have hbase : r = (fun e => α e * μ 1 + β e) := by
      simpa [r, Function.update_self] using hpath (μ 1)
    rw [← hbase] at hderiv
    rw [hvalue] at hderiv
    have hfun : (fun t => finiteChiBar q n₁ n₂ (Function.update μ 1 t)) =
        (fun t => supportMean F (fun e => α e * t + β e)) := by
      funext t
      change supportMean F (markRate n₁ n₂ (Function.update μ 1 t)) = _
      rw [hpath t]
    rw [← hfun] at hderiv
    simpa [F, r] using hderiv
  · let N : ℝ := (n₂ : ℝ)
    let d : ℝ := N ^ 2
    let F : Finset (TaggedMark n₁ n₂) → ℝ := fun T =>
      indicator (Colorable q (supportGraph T))
    let r : TaggedMark n₁ n₂ → ℝ := markRate n₁ n₂ μ
    let α : TaggedMark n₁ n₂ → ℝ := fun e =>
      match e with
      | .inl _ => 0
      | .inr (.inl _) => 0
      | .inr (.inr _) => 1 / d
    let β : TaggedMark n₁ n₂ → ℝ := fun e => r e - α e * μ 2
    have hpath (t : ℝ) : markRate n₁ n₂ (Function.update μ 2 t) =
        fun e => α e * t + β e := by
      funext e
      cases e with
      | inl xy => simp [markRate, ThresholdFoundations.interpolationMarkRate, α, β, r]
      | inr z => cases z with
        | inl xy => simp [markRate, ThresholdFoundations.interpolationMarkRate, α, β, r]
        | inr xy => simp [markRate, ThresholdFoundations.interpolationMarkRate, α, β, r, d, N]; ring
    have hA : Fintype.card (Fin n₂ × Fin n₂) ≠ 0 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
    have hd : d ≠ 0 := by dsimp [d, N]; positivity
    have hcard : (Fintype.card (Fin n₂ × Fin n₂) : ℝ) = d := by
      simp [d, N, Fintype.card_prod]
      ring
    have hsumα :
        (∑ e : TaggedMark n₁ n₂,
          α e * supportMean (fun T => F (insert e T) - F T) r) =
          (1 / d) * ∑ xy : Fin n₂ × Fin n₂,
            supportMean (fun T => F (insert (.inr (.inr xy)) T) - F T) r := by
      simp only [Fintype.sum_sum_type, α, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
      rw [← Finset.mul_sum]
    have hloss :
        (∑ xy : Fin n₂ × Fin n₂,
          supportMean (fun T => F (insert (.inr (.inr xy)) T) - F T) r) =
          -(Fintype.card (Fin n₂ × Fin n₂) : ℝ) *
            supportMean (fun T => addLoss q n₁ n₂ 2 (supportGraph T)) r := by
      simpa [F] using sum_insert_increment_eq_addLoss h10 q hq
        (Fin n₂ × Fin n₂) hA r
        (fun xy => Sum.inr (Sum.inr xy))
        (fun xy => rightVertex n₁ n₂ xy.1) (fun xy => rightVertex n₁ n₂ xy.2)
        2 (by intro a; rfl) (by intro T; rfl)
    have hvalue :
        (∑ e : TaggedMark n₁ n₂,
          α e * supportMean (fun T => F (insert e T) - F T) r) =
          -supportMean (fun T => addLoss q n₁ n₂ 2 (supportGraph T)) r := by
      rw [hsumα, hloss, hcard]
      field_simp [hd]
    have hderiv := supportMean_affine_deriv_of_I12a h12 F α β (μ 2)
    have hbase : r = (fun e => α e * μ 2 + β e) := by
      simpa [r, Function.update_self] using hpath (μ 2)
    rw [← hbase] at hderiv
    rw [hvalue] at hderiv
    have hfun : (fun t => finiteChiBar q n₁ n₂ (Function.update μ 2 t)) =
        (fun t => supportMean F (fun e => α e * t + β e)) := by
      funext t
      change supportMean F (markRate n₁ n₂ (Function.update μ 2 t)) = _
      rw [hpath t]
    rw [← hfun] at hderiv
    simpa [F, r] using hderiv

example : SA_I10Statement → SA_I12aStatement → SA_I16aStatement :=
  SA_I16aStatement_of_deps

end ThLean.W.SA36

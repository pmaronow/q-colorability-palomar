import ThLean.BP.S5.Poisson

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S555
open ThresholdFoundations ThLean.BP.S5

private lemma uniformMean_indicator_bounds {A : Type} [Fintype A] [Nonempty A]
    (P : A → Prop) :
    0 ≤ uniformMean (fun a => indicator (P a)) ∧
      uniformMean (fun a => indicator (P a)) ≤ 1 := by
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty A›
  constructor
  · unfold uniformMean
    apply div_nonneg
    · exact Finset.sum_nonneg fun a ha => by
        by_cases h : P a <;> simp [indicator, h]
    · positivity
  · unfold uniformMean
    apply (div_le_iff₀ hcard).2
    calc
      (∑ a, indicator (P a)) ≤ ∑ _a : A, (1 : ℝ) :=
        Finset.sum_le_sum fun a ha => by
          by_cases h : P a <;> simp [indicator, h]
      _ = 1 * (Fintype.card A : ℝ) := by simp

private lemma uniformMean_add {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_add_distrib]
  ring

private lemma uniformMean_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty A›)
  unfold uniformMean
  simp [hcard]

private def prefixLastEquiv {V : Type} (j : ℕ) :
    (Fin (j + 1) → V) ≃ (Fin j → V) × V :=
  let e₁ : (Fin (j + 1) → V) ≃ (Option (Fin j) → V) :=
    Equiv.arrowCongr (finSuccEquivLast (n := j)) (Equiv.refl V)
  let e₂ : (Option (Fin j) → V) ≃ ((Fin j → V) × V) :=
    (Equiv.piOptionEquivProd (β := fun _ : Option (Fin j) => V)).trans
      (Equiv.prodComm V (Fin j → V))
  e₁.trans e₂

private lemma prefixLastEquiv_castSucc {V : Type} (j : ℕ)
    (x : Fin (j + 1) → V) (i : Fin j) :
    (prefixLastEquiv j x).1 i = x i.castSucc := by
  simp [prefixLastEquiv]

private lemma prefixLastEquiv_last {V : Type} (j : ℕ)
    (x : Fin (j + 1) → V) :
    (prefixLastEquiv j x).2 = x (Fin.last j) := by
  simp [prefixLastEquiv]

private lemma prefixLastEquiv_symm_castSucc {V : Type} (j : ℕ)
    (p : (Fin j → V) × V) (i : Fin j) :
    (prefixLastEquiv j).symm p i.castSucc = p.1 i := by
  simp [prefixLastEquiv]

private lemma prefixLastEquiv_symm_last {V : Type} (j : ℕ)
    (p : (Fin j → V) × V) :
    (prefixLastEquiv j).symm p (Fin.last j) = p.2 := by
  simp [prefixLastEquiv]

private lemma ofFn_prefix_append_last {V : Type} (j : ℕ)
    (x : Fin (j + 1) → V) :
    List.ofFn (fun i : Fin j => x i.castSucc) ++ [x (Fin.last j)] = List.ofFn x := by
  revert x
  induction j with
  | zero => intro x; simp
  | succ j ih =>
      intro x
      have htail := ih (fun i : Fin (j + 1) => x i.succ)
      simpa [List.ofFn_succ, Fin.castSucc_succ, Fin.last] using htail

private lemma ofFn_prefixLast_symm {V : Type} (j : ℕ)
    (xs : Fin j → V) (v : V) :
    List.ofFn ((prefixLastEquiv j).symm (xs, v)) = List.ofFn xs ++ [v] := by
  calc
    List.ofFn ((prefixLastEquiv j).symm (xs, v)) =
        List.ofFn (fun i : Fin j => (prefixLastEquiv j).symm (xs, v) i.castSucc) ++
          [((prefixLastEquiv j).symm (xs, v)) (Fin.last j)] :=
      (ofFn_prefix_append_last j _).symm
    _ = List.ofFn xs ++ [v] := by
      simp [prefixLastEquiv_symm_castSucc, prefixLastEquiv_symm_last]

private lemma uniformMean_prefixLast {V : Type} [Fintype V] [Nonempty V]
    (hfinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0})
    (j : ℕ) (f : (Fin (j + 1) → V) → ℝ) :
    uniformMean f = uniformMean (fun xs : Fin j → V =>
      uniformMean (fun v : V => f ((prefixLastEquiv j).symm (xs, v)))) := by
  let e : (Fin (j + 1) → V) ≃ ((Fin j → V) × V) := prefixLastEquiv j
  have hrew : uniformMean f = uniformMean (fun p : (Fin j → V) × V => f (e.symm p)) := by
    have h := hfinite.1 (Fin (j + 1) → V) ((Fin j → V) × V)
      e (fun p => f (e.symm p))
    simpa [Function.comp_def, e] using h
  rw [hrew]
  exact hfinite.2.1 (Fin j → V) V
    (fun p : (Fin j → V) × V => f (e.symm p))

private lemma colorable_addRoot_base {V : Type} [Fintype V] (q : ℕ) (hq : 3 ≤ q)
    (h01 : S5_01AStatement) (B : MGraph V) (xs : List V) :
    Colorable q (addRoot B xs) → Colorable q B := by
  rintro ⟨τ, hτ⟩
  rcases (h01 V q hq B xs τ).1 hτ with ⟨hB, _⟩
  exact ⟨fun v => τ (some v), hB⟩

private lemma colorable_addRoot_mono {V : Type} [Fintype V] (q : ℕ) (hq : 3 ≤ q)
    (h01 : S5_01AStatement) (B : MGraph V) (xs : List V) (v : V) :
    Colorable q (addRoot B (xs ++ [v])) → Colorable q (addRoot B xs) := by
  rintro ⟨τ, hτ⟩
  have h := (h01 V q hq B (xs ++ [v]) τ).1 hτ
  refine ⟨τ, (h01 V q hq B xs τ).2 ?_⟩
  refine ⟨h.1, ?_⟩
  intro w hw
  exact h.2 w (by simp [hw])

private lemma blocking_append_indicator {V : Type} [Fintype V] (q : ℕ)
    (hq : 3 ≤ q) (h01 : S5_01AStatement) (B : MGraph V) (xs : List V) (v : V) :
    indicator (Colorable q B ∧ ¬ Colorable q (addRoot B (xs ++ [v]))) =
      indicator (Colorable q B ∧ ¬ Colorable q (addRoot B xs)) +
      indicator (Colorable q (addRoot B xs) ∧
        ¬ Colorable q (addRoot B (xs ++ [v]))) := by
  classical
  by_cases hb : Colorable q B
  · by_cases hp : Colorable q (addRoot B xs)
    · by_cases he : Colorable q (addRoot B (xs ++ [v]))
      · simp [indicator, hb, hp, he]
      · simp [indicator, hb, hp, he]
    · have he : ¬ Colorable q (addRoot B (xs ++ [v])) := by
        intro h
        exact hp (colorable_addRoot_mono q hq h01 B xs v h)
      simp [indicator, hb, hp, he]
  · have hp : ¬ Colorable q (addRoot B xs) := by
      intro h
      exact hb (colorable_addRoot_base q hq h01 B xs h)
    have he : ¬ Colorable q (addRoot B (xs ++ [v])) := by
      intro h
      exact hb (colorable_addRoot_base q hq h01 B (xs ++ [v]) h)
    have ht : ¬ (Colorable q (addRoot B xs) ∧
        ¬ Colorable q (addRoot B (xs ++ [v]))) := fun h => hp h.1
    simp [indicator, hb, hp, he, ht]

private lemma blocking_zero {V : Type} [Fintype V] [Nonempty V]
    (q : ℕ) (hq : 3 ≤ q) (h01 : S5_01AStatement) (B : MGraph V) :
    blocking q B 0 = 0 := by
  classical
  have hroot : Colorable q B → Colorable q (addRoot B []) := by
    rintro ⟨σ, hσ⟩
    let τ : Option V → Fin q := fun z => z.elim ⟨0, by omega⟩ σ
    refine ⟨τ, ?_⟩
    exact (h01 V q hq B [] τ).mpr ⟨hσ, by simp⟩
  unfold blocking listMean uniformMean
  have hsum : (∑ x : Fin 0 → V,
      indicator (Colorable q B ∧ ¬ Colorable q (addRoot B (List.ofFn x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hl : List.ofFn x = [] := by simp
    by_cases hb : Colorable q B
    · have hc := hroot hb
      simp [indicator, hb, hc, hl]
    · simp [indicator, hb]
  rw [hsum]
  simp

private lemma blocking_recurrence {V : Type} [Fintype V] [Nonempty V]
    (q : ℕ) (hq : 3 ≤ q) (h01 : S5_01AStatement)
    (hfinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0})
    (B : MGraph V) (j : ℕ) :
    blocking q B (j + 1) = blocking q B j + increment q B j := by
  let e : (Fin (j + 1) → V) ≃ ((Fin j → V) × V) := prefixLastEquiv j
  let f := fun x : Fin (j + 1) → V =>
    indicator (Colorable q B ∧ ¬ Colorable q (addRoot B (List.ofFn x)))
  let pre := fun xs : Fin j → V =>
    indicator (Colorable q B ∧ ¬ Colorable q (addRoot B (List.ofFn xs)))
  let step := fun xs : Fin j → V => fun v : V =>
    indicator (Colorable q (addRoot B (List.ofFn xs)) ∧
      ¬ Colorable q (addRoot B (List.ofFn xs ++ [v])))
  have hsplit : ∀ xs v, f (e.symm (xs, v)) = pre xs + step xs v := by
    intro xs v
    dsimp [f, pre, step]
    rw [ofFn_prefixLast_symm]
    exact blocking_append_indicator q hq h01 B (List.ofFn xs) v
  have hblock : blocking q B (j + 1) = uniformMean (fun xs : Fin j → V =>
      uniformMean (fun v : V => f (e.symm (xs, v)))) := by
    exact uniformMean_prefixLast hfinite j f
  have hinc : increment q B j = uniformMean (fun xs : Fin j → V =>
      uniformMean (fun v : V => step xs v)) := by
    have h := uniformMean_prefixLast hfinite j
      (fun x : Fin (j + 1) → V =>
        indicator (Colorable q (addRoot B
          (List.ofFn (fun i : Fin j => x i.castSucc))) ∧
          ¬ Colorable q (addRoot B (List.ofFn x))))
    have hdef : increment q B j = uniformMean (fun x : Fin (j + 1) → V =>
        indicator (Colorable q (addRoot B
          (List.ofFn (fun i : Fin j => x i.castSucc))) ∧
          ¬ Colorable q (addRoot B (List.ofFn x)))) := rfl
    rw [← hdef] at h
    rw [h]
    apply congrArg uniformMean
    funext xs
    apply congrArg uniformMean
    funext v
    dsimp [step]
    have hpre : (fun i : Fin j => (prefixLastEquiv j).symm (xs, v) i.castSucc) = xs := by
      funext i
      exact prefixLastEquiv_symm_castSucc j (xs, v) i
    rw [hpre, ofFn_prefixLast_symm]
  calc
    blocking q B (j + 1) = uniformMean (fun xs : Fin j → V =>
        uniformMean (fun v : V => f (e.symm (xs, v)))) := hblock
    _ = uniformMean (fun xs : Fin j → V =>
        uniformMean (fun v : V => pre xs + step xs v)) := by
          apply congrArg uniformMean
          funext xs
          apply congrArg uniformMean
          funext v
          exact hsplit xs v
    _ = uniformMean pre + increment q B j := by
          have hinner : ∀ xs : Fin j → V,
              uniformMean (fun v : V => pre xs + step xs v) =
                pre xs + uniformMean (step xs) := by
            intro xs
            simp_rw [uniformMean_add, uniformMean_const]
          rw [show uniformMean (fun xs : Fin j → V =>
              uniformMean (fun v : V => pre xs + step xs v)) =
              uniformMean (fun xs : Fin j → V => pre xs + uniformMean (step xs)) by
                apply congrArg uniformMean
                funext xs
                exact hinner xs]
          rw [uniformMean_add, hinc]
    _ = blocking q B j + increment q B j := by rfl

private lemma partnerCount_eq_frozenCard {V : Type} [Fintype V] [Nonempty V]
    (q : ℕ) (G : MGraph (Option V)) :
    partnerCount q G none =
      (Finset.univ.filter (fun v : V => Frozen q G none (some v))).card := by
  classical
  unfold partnerCount ThresholdFoundations.frozenPartnerCount
  let d : V := Classical.choice ‹Nonempty V›
  apply Finset.card_bij (fun w hw => w.getD d)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases w with _ | v
    · simp at hw
    · simpa using hw.2
  · intro w hw w' hw' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    rcases w with _ | v <;> rcases w' with _ | v' <;> simp_all
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine ⟨some v, by simpa using hv, ?_⟩
    simp

private lemma transition_uniformProb_eq_partner {V : Type} [Fintype V] [Nonempty V]
    (q : ℕ) (hq : 3 ≤ q) (h02 : S5_02Statement)
    (B : MGraph V) (hloop : Loopless B) (xs : List V) :
    uniformProb (fun v : V =>
      Colorable q (addRoot B xs) ∧
        ¬ Colorable q (addRoot B (xs ++ [v]))) =
      (partnerCount q (addRoot B xs) none : ℝ) / (Fintype.card V : ℝ) := by
  classical
  have hpoint : ∀ v : V,
      (Colorable q (addRoot B xs) ∧
        ¬ Colorable q (addRoot B (xs ++ [v]))) ↔
        Frozen q (addRoot B xs) none (some v) := by
    intro v
    constructor
    · rintro ⟨hc, hf⟩
      exact (h02 V q hq B hloop xs v hc).mpr hf
    · intro hf
      exact ⟨hf.1, (h02 V q hq B hloop xs v hf.1).mp hf⟩
  have hsum : (∑ v : V,
      indicator (Colorable q (addRoot B xs) ∧
        ¬ Colorable q (addRoot B (xs ++ [v])))) =
      (partnerCount q (addRoot B xs) none : ℝ) := by
    calc
      _ = ((Finset.univ.filter (fun v : V =>
          Frozen q (addRoot B xs) none (some v))).card : ℝ) := by
            simp [indicator, hpoint, Finset.sum_boole]
      _ = (partnerCount q (addRoot B xs) none : ℝ) := by
            rw [partnerCount_eq_frozenCard]
  unfold uniformProb uniformMean
  rw [hsum]

private lemma increment_partner_formula {V : Type} [Fintype V] [Nonempty V]
    (q : ℕ) (hq : 3 ≤ q) (h02 : S5_02Statement)
    (hfinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0})
    (B : MGraph V) (hloop : Loopless B) (j : ℕ) :
    increment q B j = (1 / (Fintype.card V : ℝ)) *
      listMean j (fun xs => (partnerCount q (addRoot B xs) none : ℝ)) := by
  have hdef : increment q B j = uniformMean (fun x : Fin (j + 1) → V =>
      indicator (Colorable q (addRoot B (List.ofFn (fun i : Fin j => x i.castSucc))) ∧
        ¬ Colorable q (addRoot B (List.ofFn x)))) := rfl
  rw [hdef]
  rw [uniformMean_prefixLast hfinite j _]
  simp_rw [prefixLastEquiv_symm_castSucc, ofFn_prefixLast_symm]
  have hinner : ∀ xs : Fin j → V,
      uniformMean (fun v : V =>
        indicator (Colorable q (addRoot B (List.ofFn xs)) ∧
          ¬ Colorable q (addRoot B (List.ofFn xs ++ [v])))) =
        (partnerCount q (addRoot B (List.ofFn xs)) none : ℝ) /
          (Fintype.card V : ℝ) := by
    intro xs
    simpa [uniformProb, uniformMean] using
      transition_uniformProb_eq_partner q hq h02 B hloop (List.ofFn xs)
  simp_rw [hinner]
  change uniformMean (fun xs : Fin j → V =>
      (partnerCount q (addRoot B (List.ofFn xs)) none : ℝ) /
        (Fintype.card V : ℝ)) =
    (1 / (Fintype.card V : ℝ)) * uniformMean (fun xs : Fin j → V =>
      (partnerCount q (addRoot B (List.ofFn xs)) none : ℝ))
  simp [uniformMean, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro xs hxs
  ring

theorem S5_13Statement_of_deps
    (h01 : S5_01AStatement) (h02 : S5_02Statement)
    (hfinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0}) :
    S5_13Statement := by
  intro V instV hV q hq B hloop
  have hzero := blocking_zero q hq h01 B
  refine ⟨hzero, ?_⟩
  intro j
  have hiBounds := uniformMean_indicator_bounds
    (fun x : Fin (j + 1) → V =>
      Colorable q (addRoot B (List.ofFn (fun i : Fin j => x i.castSucc))) ∧
        ¬ Colorable q (addRoot B (List.ofFn x)))
  have hbBounds := uniformMean_indicator_bounds
    (fun x : Fin j → V =>
      Colorable q B ∧ ¬ Colorable q (addRoot B (List.ofFn x)))
  have hrec := blocking_recurrence q hq h01 hfinite B j
  have hsumAll : ∀ j, blocking q B j = ∑ i ∈ Finset.range j, increment q B i := by
    intro j
    induction j with
    | zero => simp [blocking_zero q hq h01 B]
    | succ j ih =>
        rw [blocking_recurrence q hq h01 hfinite B j, ih, Finset.sum_range_succ]
  have hsum := hsumAll j
  refine ⟨?_, ?_, ?_, ?_, hsum, ?_⟩
  · exact hiBounds.1
  · exact hiBounds.2
  · exact hbBounds.1
  · exact hbBounds.2
  · exact increment_partner_formula q hq h02 hfinite B hloop j

end ThLean.W.S555

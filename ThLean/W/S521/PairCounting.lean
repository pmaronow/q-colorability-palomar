module

public import ThLean.BP.S5.Identification

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S521
open ThresholdFoundations
open ThLean.BP.S5
universe u v

private def pairEquivNotDiag (V : Type*) [Fintype V] : Pair V ≃ {e : Sym2 V // ¬ e.IsDiag} where
  toFun e := ⟨e.val, by
    intro hd
    exact e.property (e.val.diagElem hd) (Sym2.diag_diagElem hd).symm⟩
  invFun e := ⟨e.val, by
    intro v hv
    apply e.property
    rw [hv]
    exact Sym2.diag_isDiag v⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

lemma pair_card {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype.card (Pair V) = (Fintype.card V).choose 2 := by
  rw [Fintype.card_congr (pairEquivNotDiag V)]
  exact Sym2.card_subtype_not_diag

private lemma cast_choose_two_real (n : ℕ) :
    (n.choose 2 : ℝ) = ((n : ℝ)^2 - n) / 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Nat.cast_choose_two]
    push_cast
    ring

private abbrev ColorFiber {V : Type*} (q : ℕ) (σ : V → Fin q) (c : Fin q) :=
  {v : V // σ v = c}

private abbrev monoPairSet {V : Type*} [Fintype V] {q : ℕ} (σ : V → Fin q) :=
  {e : Pair V // ∃ u v, e.val = s(u, v) ∧ σ u = σ v}

private def mapFiberPair {V : Type*} [Fintype V] {q : ℕ} (σ : V → Fin q)
    (c : Fin q) (e : Pair (ColorFiber q σ c)) : Pair V :=
  ⟨Sym2.map Subtype.val e.val, by
    have hnd : ¬ e.val.IsDiag := by
      intro hd
      exact e.property (e.val.diagElem hd) (Sym2.diag_diagElem hd).symm
    have hmap : ¬ (Sym2.map Subtype.val e.val).IsDiag := by
      simpa only [Sym2.isDiag_map Subtype.val_injective] using hnd
    intro v heq
    apply hmap
    rw [heq]
    exact Sym2.diag_isDiag v⟩

private lemma mapFiberPair_mono {V : Type*} [Fintype V] {q : ℕ}
    (σ : V → Fin q) (c : Fin q) (e : Pair (ColorFiber q σ c)) :
    ∃ u v, (mapFiberPair σ c e).val = s(u, v) ∧ σ u = σ v := by
  rcases e with ⟨z, hz⟩
  change ∃ u v, Sym2.map Subtype.val z = s(u, v) ∧ σ u = σ v
  refine Sym2.inductionOn z ?_
  intro a b
  exact ⟨a.val, b.val, rfl, a.property.trans b.property.symm⟩

private def fiberPairToMono {V : Type*} [Fintype V] {q : ℕ} (σ : V → Fin q) :
    (Σ c : Fin q, Pair (ColorFiber q σ c)) → monoPairSet σ := fun x =>
  ⟨mapFiberPair σ x.1 x.2, mapFiberPair_mono σ x.1 x.2⟩

private lemma fiberPairToMono_injective {V : Type*} [Fintype V] {q : ℕ}
    (σ : V → Fin q) : Function.Injective (fiberPairToMono σ) := by
  intro x y hxy
  obtain ⟨c, e⟩ := x
  obtain ⟨d, f⟩ := y
  have hp : (fiberPairToMono σ ⟨c, e⟩).val = (fiberPairToMono σ ⟨d, f⟩).val :=
    congrArg Subtype.val hxy
  have hs : Sym2.map Subtype.val e.val = Sym2.map Subtype.val f.val :=
    congrArg Subtype.val hp
  have heout : s(e.val.out.1, e.val.out.2) = e.val := by
    simp [Sym2.mk]
  have hfout : s(f.val.out.1, f.val.out.2) = f.val := by
    simp [Sym2.mk]
  have hout : s(e.val.out.1.val, e.val.out.2.val) = s(f.val.out.1.val, f.val.out.2.val) := by
    calc
      _ = Sym2.map Subtype.val e.val := by
        symm
        calc
          Sym2.map Subtype.val e.val = Sym2.map Subtype.val (s(e.val.out.1, e.val.out.2)) :=
            congrArg (Sym2.map Subtype.val) heout.symm
          _ = _ := by simp
      _ = Sym2.map Subtype.val f.val := hs
      _ = _ := by
        calc
          Sym2.map Subtype.val f.val = Sym2.map Subtype.val (s(f.val.out.1, f.val.out.2)) :=
            congrArg (Sym2.map Subtype.val) hfout.symm
          _ = _ := by simp
  rcases Sym2.eq_iff.mp hout with hsame | hswap
  · have hfd : σ e.val.out.1.val = d := by
      have h := f.val.out.1.property
      rw [hsame.1.symm] at h
      exact h
    have hcd : c = d := e.val.out.1.property.symm.trans hfd
    cases hcd
    have hef : e.val = f.val := (Sym2.map.injective Subtype.val_injective) hs
    have he : e = f := Subtype.ext hef
    subst f
    rfl
  · have hfd : σ e.val.out.1.val = d := by
      have h := f.val.out.2.property
      rw [hswap.1.symm] at h
      exact h
    have hcd : c = d := e.val.out.1.property.symm.trans hfd
    cases hcd
    have hef : e.val = f.val := (Sym2.map.injective Subtype.val_injective) hs
    have he : e = f := Subtype.ext hef
    subst f
    rfl

private def vertexFiberEquiv {V : Type*} {q : ℕ} (σ : V → Fin q) :
    V ≃ (Σ c : Fin q, ColorFiber q σ c) where
  toFun v := ⟨σ v, ⟨v, rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨c, ⟨v, hv⟩⟩
    subst c
    rfl

private lemma uniformProb_eq_card_subtype {A : Type*} [Fintype A] (P : A → Prop) :
    uniformProb P = (Fintype.card {a // P a} : ℝ) / (Fintype.card A : ℝ) := by
  classical
  rw [uniformProb, uniformMean, Fintype.card_subtype]
  simp [indicator]

lemma monochromatic_pair_fraction {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 3 ≤ q) (hN : 2 * q ≤ Fintype.card V) (σ : V → Fin q) :
    1 / (2 * (q : ℝ)) ≤ uniformProb (fun e : Pair V =>
      ∃ u v, e.val = s(u, v) ∧ σ u = σ v) := by
  classical
  letI : DecidablePred (fun e : Pair V =>
      ∃ u v, e.val = s(u, v) ∧ σ u = σ v) := fun _ => Classical.propDecidable _
  letI : Fintype (monoPairSet σ) := by
    unfold monoPairSet
    infer_instance
  let F : Fin q → Type _ := ColorFiber q σ
  have hsumNat : (∑ c : Fin q, Fintype.card (F c)) = Fintype.card V := by
    calc
      _ = Fintype.card (Σ c : Fin q, F c) := by simp [F]
      _ = Fintype.card V := Fintype.card_congr (vertexFiberEquiv σ).symm
  have hsumReal : (∑ c : Fin q, (Fintype.card (F c) : ℝ)) = Fintype.card V := by
    rw [← Nat.cast_sum, hsumNat]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
    (fun c => (Fintype.card (F c) : ℝ)) (fun _ => (1 : ℝ))
  have hcs' : (Fintype.card V : ℝ)^2 ≤
      (q : ℝ) * ∑ c : Fin q, (Fintype.card (F c) : ℝ)^2 := by
    simpa [hsumReal, mul_comm] using hcs
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hsquare : (Fintype.card V : ℝ)^2 / (q : ℝ) ≤
      ∑ c : Fin q, (Fintype.card (F c) : ℝ)^2 := by
    apply (div_le_iff₀ hqpos).2
    nlinarith [hcs']
  have hchooseEq : (∑ c : Fin q, (Fintype.card (F c)).choose 2 : ℝ) =
      ((∑ c : Fin q, (Fintype.card (F c) : ℝ)^2) - (Fintype.card V : ℝ)) / 2 := by
    calc
      _ = ∑ c : Fin q, (((Fintype.card (F c) : ℝ)^2 - Fintype.card (F c)) / 2) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact cast_choose_two_real _
      _ = ((∑ c : Fin q, (Fintype.card (F c) : ℝ)^2) -
          ∑ c : Fin q, (Fintype.card (F c) : ℝ)) / 2 := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_sub_distrib]
      _ = _ := by rw [hsumReal]
  have hchooseLower : ((Fintype.card V : ℝ)^2 / (q : ℝ) - Fintype.card V) / 2 ≤
      (∑ c : Fin q, (Fintype.card (F c)).choose 2 : ℝ) := by
    rw [hchooseEq]
    linarith [hsquare]
  have hmonoCard : (∑ c : Fin q, (Fintype.card (F c)).choose 2) ≤
      Fintype.card (monoPairSet σ) := by
    calc
      _ = Fintype.card (Σ c : Fin q, Pair (F c)) := by simp [F, pair_card]
      _ ≤ Fintype.card (monoPairSet σ) :=
        Fintype.card_le_of_injective (fiberPairToMono σ) (fiberPairToMono_injective σ)
  have hmonoLower : ((Fintype.card V : ℝ)^2 / (q : ℝ) - Fintype.card V) / 2 ≤
      (Fintype.card (monoPairSet σ) : ℝ) := by
    exact hchooseLower.trans (by exact_mod_cast hmonoCard)
  rw [uniformProb_eq_card_subtype, pair_card, cast_choose_two_real]
  have hNreal : 2 * (q : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have hqReal : 3 ≤ (q : ℝ) := by exact_mod_cast hq
  have hNnat : 0 < Fintype.card V := by omega
  have hNpos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hNnat
  have hden : 0 < ((Fintype.card V : ℝ)^2 - Fintype.card V) / 2 := by
    have hn : 1 < (Fintype.card V : ℝ) := by nlinarith [hqReal, hNreal]
    have hp := mul_pos hNpos (sub_pos.mpr hn)
    nlinarith [hp]
  apply (le_div_iff₀ hden).2
  have hprod : 0 ≤ (Fintype.card V : ℝ) *
      ((Fintype.card V : ℝ) - 2 * (q : ℝ)) :=
    mul_nonneg (le_of_lt hNpos) (sub_nonneg.mpr hNreal)
  have hfactor : (1 / (2 * (q : ℝ))) *
      (((Fintype.card V : ℝ)^2 - Fintype.card V) / 2) ≤
      ((Fintype.card V : ℝ)^2 / (q : ℝ) - Fintype.card V) / 2 := by
    field_simp [hqpos.ne']
    nlinarith [hprod]
  exact hfactor.trans hmonoLower

lemma uniformProb_nonneg {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProb P := by
  unfold uniformProb uniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro a ha
    by_cases hp : P a <;> simp [indicator, hp]
  · positivity

lemma uniformProb_compl {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    uniformProb (fun a => ¬ P a) = 1 - uniformProb P := by
  classical
  have hsum : Finset.univ.sum (fun a : A => indicator (P a) + indicator (¬ (P a))) =
      Fintype.card A := by
    calc
      _ = Finset.univ.sum (fun _a : A => (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hp : P a <;> simp [indicator, hp]
      _ = _ := by simp
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hsum' : (Finset.univ.sum fun a : A => indicator (P a)) +
      (Finset.univ.sum fun a : A => indicator (¬ (P a))) =
      Fintype.card A := by
    rw [← Finset.sum_add_distrib]
    exact hsum
  unfold uniformProb uniformMean
  field_simp [hcard]
  nlinarith [hsum']

lemma uniformProb_prod {A B : Type u} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (hfinite : ThresholdFoundations.PreFiniteLawsStatement.{u, u})
    (P : A → Prop) (Q : B → Prop) :
    uniformProb (fun x : A × B => P x.1 ∧ Q x.2) = uniformProb P * uniformProb Q := by
  rcases hfinite with ⟨_, hfub, _, _⟩
  have hinner (a : A) :
      uniformMean (fun b : B => indicator (P a ∧ Q b)) = indicator (P a) * uniformProb Q := by
    by_cases hp : P a
    · simp [uniformMean, uniformProb, indicator, hp]
    · simp [uniformMean, indicator, hp]
  calc
    uniformProb (fun x : A × B => P x.1 ∧ Q x.2) =
        uniformMean (fun a => uniformMean (fun b => indicator (P a ∧ Q b))) := by
      unfold uniformProb
      exact hfub A B (fun x : A × B => indicator (P x.1 ∧ Q x.2))
    _ = uniformMean (fun a => indicator (P a) * uniformProb Q) := by
      congr 1
      funext a
      exact hinner a
    _ = uniformProb P * uniformProb Q := by
      simp only [uniformMean, uniformProb, div_eq_mul_inv]
      rw [← Finset.sum_mul]
      ring

lemma uniformProb_exists_le {A B : Type*} [Fintype A] [Nonempty A] [Fintype B]
    (P : B → A → Prop) :
    uniformProb (fun a => ∃ b, P b a) ≤ ∑ b, uniformProb (P b) := by
  classical
  have hden : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  unfold uniformProb uniformMean
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hden).2
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hex : ∃ b, P b a
  · obtain ⟨b, hb⟩ := hex
    have hex' : ∃ b, P b a := ⟨b, hb⟩
    have hbmem : b ∈ (Finset.univ : Finset B) := Finset.mem_univ _
    have hnon : ∀ c ∈ (Finset.univ : Finset B), 0 ≤ indicator (P c a) := by
      intro c hc
      by_cases hpc : P c a <;> simp [indicator, hpc]
    have hs : (1 : ℝ) ≤ ∑ b : B, indicator (P b a) := by
      calc
        _ = indicator (P b a) := by simp [indicator, hb]
        _ ≤ ∑ c : B, indicator (P c a) := Finset.single_le_sum hnon hbmem
    have hleft : indicator (∃ b, P b a) = 1 := by simp [indicator, hex']
    rw [hleft]
    exact hs
  · have hs : 0 ≤ ∑ b : B, indicator (P b a) :=
      Finset.sum_nonneg fun b _ => by
        by_cases hb : P b a <;> simp [indicator, hb]
    have hleft : indicator (∃ b, P b a) = 0 := by simp [indicator, hex]
    rw [hleft]
    exact hs


end ThLean.W.S521

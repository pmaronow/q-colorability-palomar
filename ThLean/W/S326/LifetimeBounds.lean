module

public import ThLean.BP.S3.Lifetime

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ThLean.W.S326
open ThresholdFoundations ThLean.BP.S3
attribute [local instance] Classical.propDecidable
universe u

private def avoidsMap {V : Type*} [Fintype V] {q : ℕ}
    (σ : V → Fin q) (e : Pair V) : Prop :=
  ¬ ∃ u v, e.val = s(u,v) ∧ σ u = σ v

private def avoidsTuple {V : Type*} [Fintype V] {q k : ℕ}
    (σ : V → Fin q) (x : EdgeTuple V k) : Prop :=
  ∀ i, avoidsMap σ (x i)

private theorem uniformProb_compl {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    uniformProb (fun a => ¬ P a) = 1 - uniformProb P := by
  classical
  unfold uniformProb uniformMean indicator
  have hsum : (∑ a, (if ¬ P a then (1 : ℝ) else 0)) +
      (∑ a, (if P a then (1 : ℝ) else 0)) = (Fintype.card A : ℝ) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ a, ((if ¬ P a then (1 : ℝ) else 0) + (if P a then (1 : ℝ) else 0))) =
          ∑ a, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : P a <;> simp [h]
      _ = _ := by simp
  have hNpos : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hN : (Fintype.card A : ℝ) ≠ 0 := ne_of_gt hNpos
  field_simp
  rw [← hsum]
  ring

private theorem uniformProb_avoidsMap {V : Type*} [Fintype V] [Nonempty (Pair V)]
    {q : ℕ} (σ : V → Fin q) :
    uniformProb (avoidsMap σ) = 1 - monoPairProb σ := by
  exact uniformProb_compl (fun e : Pair V => ∃ u v, e.val = s(u,v) ∧ σ u = σ v)

private theorem uniformProb_avoidsTuple {V : Type*} [Fintype V] [Nonempty (Pair V)]
    {q k : ℕ} (σ : V → Fin q) :
    uniformProb (avoidsTuple (k := k) σ) = (1 - monoPairProb σ) ^ k := by
  classical
  let A : Type _ := {e : Pair V // avoidsMap σ e}
  let e : (Fin k → A) ≃ {x : EdgeTuple V k // avoidsTuple (k := k) σ x} :=
    { toFun := fun x => ⟨fun i => (x i).val, fun i => (x i).property⟩
      invFun := fun x i => ⟨x.1 i, x.2 i⟩
      left_inv := by intro x; funext i; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  have hgood : Fintype.card {x : EdgeTuple V k // avoidsTuple (k := k) σ x} =
      Fintype.card A ^ k := by
    calc
      _ = Fintype.card (Fin k → A) := (Fintype.card_congr e).symm
      _ = Fintype.card A ^ k := by simp [Fintype.card_fun]
  have hgoodSum : (∑ x : EdgeTuple V k, indicator (avoidsTuple (k := k) σ x)) =
      (Fintype.card A : ℝ) ^ k := by
    calc
      _ = (Fintype.card {x : EdgeTuple V k // avoidsTuple (k := k) σ x} : ℝ) := by
        simp [indicator, Fintype.card_subtype, Finset.sum_boole]
      _ = (Fintype.card A : ℝ) ^ k := by
        rw [hgood]
        norm_cast
  have hsingle : uniformProb (avoidsMap σ) =
      (Fintype.card A : ℝ) / (Fintype.card (Pair V) : ℝ) := by
    have hA : Fintype.card A = (Finset.univ.filter (avoidsMap σ)).card := by
      simp [A, Fintype.card_subtype]
    unfold uniformProb uniformMean
    rw [show (∑ e : Pair V, indicator (avoidsMap σ e)) =
      (Fintype.card A : ℝ) by
        calc
          _ = ((Finset.univ.filter (avoidsMap σ)).card : ℝ) := by
            simp [indicator, Finset.sum_boole]
          _ = _ := by rw [hA]]
  unfold uniformProb uniformMean
  rw [hgoodSum]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [← div_pow, ← hsingle, uniformProb_avoidsMap]

private theorem uniformProb_le_sum {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    (P : A → Prop) (Q : I → A → Prop)
    (hcover : ∀ a, P a → ∃ i, Q i a) :
    uniformProb P ≤ ∑ i, uniformProb (Q i) := by
  classical
  have hpoint (a : A) : indicator (P a) ≤ ∑ i, indicator (Q i a) := by
    by_cases hp : P a
    · rcases hcover a hp with ⟨i, hi⟩
      have hterm : indicator (Q i a) = (1 : ℝ) := by simp [indicator, hi]
      have hsum : indicator (Q i a) ≤ ∑ j, indicator (Q j a) := by
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun j : I => indicator (Q j a))
          (fun j hj => by unfold indicator; split_ifs <;> norm_num)
          (Finset.mem_univ i)
      calc
        indicator (P a) = 1 := by simp [indicator, hp]
        _ = indicator (Q i a) := hterm.symm
        _ ≤ ∑ j, indicator (Q j a) := hsum
    · simp [indicator, hp]
  have hsum : (∑ a : A, indicator (P a)) ≤
      (∑ a : A, ∑ i : I, indicator (Q i a)) :=
    Finset.sum_le_sum (fun a ha => hpoint a)
  have hNpos : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hrew : (∑ i, (∑ a, indicator (Q i a)) / (Fintype.card A : ℝ)) =
      (∑ a, ∑ i, indicator (Q i a)) / (Fintype.card A : ℝ) := by
    rw [← Finset.sum_div]
    apply congrArg (fun z : ℝ => z / (Fintype.card A : ℝ))
    simpa using (Finset.sum_comm
      (s := (Finset.univ : Finset I)) (t := (Finset.univ : Finset A))
      (f := fun i a => indicator (Q i a)))
  unfold uniformProb uniformMean
  calc
    (∑ a, indicator (P a)) / (Fintype.card A : ℝ) ≤
        (∑ a, ∑ i, indicator (Q i a)) / (Fintype.card A : ℝ) :=
      div_le_div_of_nonneg_right hsum (le_of_lt hNpos)
    _ = ∑ i, (∑ a, indicator (Q i a)) / (Fintype.card A : ℝ) := hrew.symm

private theorem uniformProb_le_one {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) : uniformProb P ≤ 1 := by
  classical
  have hsum : (∑ a : A, indicator (P a)) ≤ (Fintype.card A : ℝ) := by
    calc
      _ ≤ ∑ _a : A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases h : P a <;> simp [indicator, h]
      _ = _ := by simp
  have hNpos : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold uniformProb uniformMean
  calc
    (∑ a, indicator (P a)) / (Fintype.card A : ℝ) ≤
        (Fintype.card A : ℝ) / (Fintype.card A : ℝ) :=
      div_le_div_of_nonneg_right hsum (le_of_lt hNpos)
    _ = 1 := div_self (ne_of_gt hNpos)

private theorem uniformProb_nonneg {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProb P := by
  classical
  unfold uniformProb uniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro a ha
    unfold indicator
    split_ifs <;> positivity
  · positivity

private theorem pair_nonempty_of_card {V : Type*} [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  classical
  have hn : 1 < Fintype.card V := by omega
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card hn
  refine ⟨⟨s(u,v), ?_⟩⟩
  intro w he
  have hdiag : Sym2.IsDiag (s(u,v)) := by
    rw [he]
    simp
  have huv' : u = v := by simpa only [Sym2.mk_isDiag_iff] using hdiag
  exact huv huv'

private theorem colorable_avoidsTuple {V : Type*} [Fintype V] {q k : ℕ}
    (G : MGraph V) (x : EdgeTuple V k) (h : Colorable q (G + tupleGraph x)) :
    ∃ σ : V → Fin q, avoidsTuple (k := k) σ x := by
  classical
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, ?_⟩
  intro i hbad
  obtain ⟨u, v, he, hsame⟩ := hbad
  have hposT : 0 < tupleGraph x (s(u,v)) := by
    rw [← he]
    unfold tupleGraph
    apply Finset.card_pos.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hle : tupleGraph x (s(u,v)) ≤ (G + tupleGraph x) (s(u,v)) := by
    change tupleGraph x (s(u,v)) ≤ G (s(u,v)) + tupleGraph x (s(u,v))
    exact Nat.le_add_left _ _
  exact (hσ u v (lt_of_lt_of_le hposT hle)) hsame

/-- The first-moment survival estimate from the monochromatic-pair bound. -/
theorem S3_24Statement_of_deps (h23 : S3_23Statement.{u}) :
    S3_24Statement.{u} := by
  classical
  intro V _ q hq hV G k
  letI : Nonempty (Pair V) := pair_nonempty_of_card hV
  letI : Nonempty (EdgeTuple V k) := ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair V))⟩
  have hcoverage : ∀ x : EdgeTuple V k,
      Colorable q (G + tupleGraph x) → ∃ σ : V → Fin q, avoidsTuple (k := k) σ x :=
    fun x hx => colorable_avoidsTuple G x hx
  have hsumBound (b : ℝ) (hb : 0 ≤ b)
      (hbase : ∀ σ : V → Fin q, 1 - monoPairProb σ ≤ b) :
      survival q G k ≤ (q : ℝ) ^ Fintype.card V * b ^ k := by
    calc
      survival q G k ≤ ∑ σ : V → Fin q, uniformProb (avoidsTuple (k := k) σ) :=
        uniformProb_le_sum _ _ hcoverage
      _ ≤ ∑ σ : V → Fin q, b ^ k := by
        apply Finset.sum_le_sum
        intro σ hσ
        rw [uniformProb_avoidsTuple]
        have hnonneg : 0 ≤ 1 - monoPairProb σ := by
          rw [← uniformProb_avoidsMap]
          exact uniformProb_nonneg _
        exact pow_le_pow_left₀ hnonneg (hbase σ) k
      _ = (q : ℝ) ^ Fintype.card V * b ^ k := by
        simp [Fintype.card_fun, Nat.cast_pow]
  have hfirst (σ : V → Fin q) := h23 V q hq hV σ
  have hfactor : ∀ σ : V → Fin q,
      1 - monoPairProb σ ≤ (((q : ℝ) - 1) / q) *
        ((Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 1)) := by
    intro σ
    exact (hfirst σ).2.2.2
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hNR : 1 < (Fintype.card V : ℝ) := by
    exact_mod_cast (show 1 < Fintype.card V by omega)
  have hqminus : 0 ≤ (q : ℝ) - 1 := by linarith
  have hNminus : 0 < (Fintype.card V : ℝ) - 1 := by linarith
  have hb1 : 0 ≤ (((q : ℝ) - 1) / q) *
        ((Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 1)) := by positivity
  have h1 := hsumBound _ hb1 hfactor
  have hlarge : 2*q ≤ Fintype.card V →
      survival q G k ≤ min 1 ((q : ℝ) ^ Fintype.card V * Real.exp (-(k : ℝ)/(2*q))) := by
    intro hN
    have hNpair (σ : V → Fin q) := (hfirst σ).2.2.1 hN
    have hbase2 : ∀ σ : V → Fin q, 1 - monoPairProb σ ≤ 1 - 1/(2*(q : ℝ)) := by
      intro σ
      have := hNpair σ
      linarith
    have hb2 : 0 ≤ 1 - 1/(2*(q : ℝ)) := by
      have hden : 1 ≤ 2 * (q : ℝ) := by nlinarith [hqR2]
      exact sub_nonneg.mpr (div_le_one_of_le₀ hden (by positivity))
    have hgeom := hsumBound _ hb2 hbase2
    have hexp : (1 - 1/(2*(q : ℝ))) ^ k ≤ Real.exp (-(k : ℝ)/(2*q)) := by
      have hsingle := Real.one_sub_le_exp_neg (1/(2*(q : ℝ)))
      have hpow := pow_le_pow_left₀ hb2 hsingle k
      calc
        _ ≤ (Real.exp (-(1/(2*(q : ℝ)))) : ℝ) ^ k := hpow
        _ = Real.exp (-(k : ℝ)/(2*q)) := by
          rw [← Real.exp_nat_mul]
          push_cast
          ring
    have hprod : (q : ℝ) ^ Fintype.card V *
        (1 - 1/(2*(q : ℝ))) ^ k ≤
        (q : ℝ) ^ Fintype.card V * Real.exp (-(k : ℝ)/(2*q)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    exact le_min (uniformProb_le_one _) (hgeom.trans hprod)
  have hthird : 2*q ≤ Fintype.card V →
      survival q G k ≤ (q : ℝ) ^ Fintype.card V * (1-1/(2*(q : ℝ)))^k := by
    intro hN
    apply hsumBound _ (by
      have hden : 1 ≤ 2 * (q : ℝ) := by nlinarith [hqR2]
      exact sub_nonneg.mpr (div_le_one_of_le₀ hden (by positivity)))
    intro σ
    have := (hfirst σ).2.2.1 hN
    linarith
  exact ⟨h1, hlarge, hthird⟩

end ThLean.W.S326

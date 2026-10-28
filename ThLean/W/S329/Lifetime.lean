import ThLean.BP.S3.Lifetime

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S329
open ThresholdFoundations

private def uniformProbENN {A : Type*} [Fintype A] (P : A → Prop) : ℝ≥0∞ :=
  uniformMeanENN (fun a => if P a then 1 else 0)

private lemma uniformProbENN_eq {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    uniformProbENN P = ENNReal.ofReal (uniformProb P) := by
  classical
  have hc : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsumENN : (∑ a : A, (if P a then (1 : ℝ≥0∞) else 0)) =
      ENNReal.ofReal (∑ a : A, indicator (P a)) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro a ha
      by_cases h : P a <;> simp [indicator, h]
    · intro a ha
      by_cases h : P a <;> simp [indicator, h]
  unfold uniformProbENN uniformMeanENN uniformProb uniformMean
  rw [hsumENN, ENNReal.ofReal_div_of_pos hc]
  simp

private lemma uniformProb_nonneg {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    0 ≤ uniformProb P := by
  classical
  unfold uniformProb uniformMean indicator
  apply div_nonneg
  · exact Finset.sum_nonneg fun a _ => by split_ifs <;> norm_num
  · exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A).le

private lemma uniformProb_not {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    uniformProb (fun a => ¬ P a) = 1 - uniformProb P := by
  classical
  have hc : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ a : A, indicator (¬ P a)) = ∑ a : A, (1 - indicator (P a)) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : P a <;> simp [indicator, h]
  unfold uniformProb uniformMean
  rw [hsum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  field_simp [ne_of_gt hc]

private lemma uniformProb_fin1 {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    uniformProb (fun y : Fin 1 → A => P (y 0)) = uniformProb P := by
  classical
  let e : (Fin 1 → A) ≃ A := Equiv.funUnique (Fin 1) A
  have hsum : (∑ y : Fin 1 → A, indicator (P (y 0))) =
      ∑ a : A, indicator (P a) := by
    apply Fintype.sum_equiv e
    intro y
    simp [e, Equiv.funUnique]
  unfold uniformProb uniformMean
  rw [Fintype.card_congr e, hsum]

private lemma tupleGraph_mono_prefix {V : Type*} [Fintype V] {k : ℕ}
    (x : EdgeTuple V (k+1)) :
    subgraph (tupleGraph (fun i : Fin k => x i.castSucc)) (tupleGraph x) := by
  intro e
  let s := Finset.univ.filter (fun i : Fin k => (x i.castSucc).val = e)
  let t := Finset.univ.filter (fun i : Fin (k+1) => (x i).val = e)
  change s.card ≤ t.card
  calc
    s.card = (s.image Fin.castSucc).card := by
      rw [Finset.card_image_of_injective s (Fin.castSucc_injective k)]
    _ ≤ t.card := by
      apply Finset.card_le_card
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi

private lemma tupleGraph_contains_coordinate {V : Type*} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (i : Fin m) : 0 < tupleGraph x (x i).val := by
  unfold tupleGraph
  apply Finset.card_pos.mpr
  refine ⟨i, Finset.mem_filter.mpr ?_⟩
  simp

private lemma uniformProb_mono {A : Type*} [Fintype A] [Nonempty A] {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : uniformProb P ≤ uniformProb Q := by
  classical
  unfold uniformProb uniformMean indicator
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun a _ => by
      by_cases hp : P a
      · have hq := h a hp
        simp [hp, hq]
      · by_cases hq : Q a <;> simp [hp, hq]
  · exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A).le

private lemma survival_step {V : Type u} [Fintype V] (h2 : ThLean.BP.S3.S3_02Statement.{u})
    (h9 : ThLean.BP.S3.S3_09bStatement.{u, u}) (q : ℕ) (hq : 2 ≤ q)
    (hV : 2 ≤ Fintype.card V) (G : MGraph V) (k : ℕ) :
    survival q G (k+1) ≤ survival q G k * (1-kappa q G) := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega : 1 < Fintype.card V)
  letI : Nonempty (Pair V) := by
    obtain ⟨u, v, huv⟩ := exists_pair_ne V
    exact ⟨⟨s(u,v), by
      intro w hw
      rcases Sym2.eq_iff.mp hw with h | h
      · rcases h with ⟨huw, hvw⟩
        exact huv (huw.trans hvw.symm)
      · rcases h with ⟨huw, hvw⟩
        exact huv (huw.trans hvw.symm)⟩⟩
  let pref : EdgeTuple V k → MGraph V := fun y => tupleGraph y
  let A : (EdgeTuple V k → Prop) := fun y => Colorable q (G + pref y)
  let B : Pair V → Prop := fun e => ¬ FrozenPair q G e
  let B1 : (Fin 1 → Pair V) → Prop := fun y => B (y 0)
  let f : (Fin k → Pair V) → ℝ≥0∞ := fun y => if A y then 1 else 0
  let g : (Fin 1 → Pair V) → ℝ≥0∞ := fun y => if B1 y then 1 else 0
  let i : Fin k ↪ Fin (k+1) := Fin.castSuccEmb
  let j : Fin 1 ↪ Fin (k+1) := Fin.natAddEmb k
  have hj0raw : Fin.natAdd k (0 : Fin 1) = Fin.last k := by
    apply Fin.ext
    simp [Fin.natAdd]
  have hj0 : j 0 = Fin.last k := by
    change Fin.natAdd k (0 : Fin 1) = Fin.last k
    exact hj0raw
  have hdisj : Disjoint (Set.range i) (Set.range j) := by
    rw [Set.disjoint_left]
    rintro z ⟨a, ha⟩ ⟨b, hb⟩
    have hlast : Fin.natAddEmb k b = Fin.last k := by
      have hb0 : b = 0 := Fin.ext (by omega)
      subst b
      change Fin.natAdd k (0 : Fin 1) = Fin.last k
      exact hj0raw
    have hlt : i a < Fin.last k := by
      simpa [i] using Fin.castSucc_lt_last a
    have heq : i a = Fin.last k := ha.trans (hb.symm.trans hlast)
    exact (Fin.ne_of_lt hlt) heq
  have h2fin := h2 (Pair V) (k+1) k i
  have hfactor := h2fin.2.2.2 k 1 i j hdisj f g
  let P : EdgeTuple V (k+1) → Prop := fun y =>
    Colorable q (G + tupleGraph (fun r : Fin k => y r.castSucc)) ∧
      ¬ FrozenPair q G (y (Fin.last k))
  have hfactor' : uniformProbENN (fun y : EdgeTuple V (k+1) =>
      Colorable q (G + tupleGraph (fun r : Fin k => y r.castSucc)) ∧
        ¬ FrozenPair q G (y (Fin.last k))) =
      uniformMeanENN f * uniformMeanENN g := by
    classical
    calc
      uniformProbENN (fun y : EdgeTuple V (k+1) =>
          Colorable q (G + tupleGraph (fun r : Fin k => y r.castSucc)) ∧
            ¬ FrozenPair q G (y (Fin.last k))) =
        uniformMeanENN (fun y : Fin (k+1) → Pair V => f (fun r => y (i r)) * g (fun r => y (j r))) := by
          unfold uniformProbENN
          apply congrArg uniformMeanENN
          funext y
          by_cases ha : Colorable q (G + tupleGraph (fun r : Fin k => y r.castSucc))
          · by_cases hb : ¬ FrozenPair q G (y (Fin.last k))
            · simp [P, f, g, A, B, B1, pref, i, j, hj0raw, ha, hb]
            · simp [P, f, g, A, B, B1, pref, i, j, hj0raw, ha, hb]
          · simp [P, f, g, A, B, B1, pref, i, j, hj0raw, ha]
      _ = uniformMeanENN f * uniformMeanENN g := hfactor
  have hfactorReal : uniformProb (fun y : EdgeTuple V (k+1) =>
      Colorable q (G + tupleGraph (fun i : Fin k => y i.castSucc)) ∧
        ¬ FrozenPair q G (y (Fin.last k))) =
      uniformProb A * uniformProb B1 := by
    have hcL : Nonempty (EdgeTuple V (k+1)) := inferInstance
    have hcA : Nonempty (EdgeTuple V k) := inferInstance
    have hcB : Nonempty (Fin 1 → Pair V) := inferInstance
    have h := hfactor'
    have hf : uniformMeanENN f = ENNReal.ofReal (uniformProb A) := by
      calc
        uniformMeanENN f = uniformProbENN A := by simp [f, uniformProbENN]
        _ = ENNReal.ofReal (uniformProb A) := uniformProbENN_eq A
    have hg : uniformMeanENN g = ENNReal.ofReal (uniformProb B1) := by
      have hgb : uniformMeanENN g = uniformProbENN B1 := by
        unfold uniformProbENN
        apply congrArg uniformMeanENN
        funext y
        by_cases hb : FrozenPair q G (y 0) <;> simp [g, B1, B, hb]
      rw [hgb, uniformProbENN_eq]
    have hleftENN : uniformProbENN (fun y : EdgeTuple V (k+1) =>
        Colorable q (G + tupleGraph (fun i : Fin k => y i.castSucc)) ∧
          ¬ FrozenPair q G (y (Fin.last k))) = ENNReal.ofReal (uniformProb (fun y : EdgeTuple V (k+1) =>
        Colorable q (G + tupleGraph (fun i : Fin k => y i.castSucc)) ∧
          ¬ FrozenPair q G (y (Fin.last k)))) := uniformProbENN_eq _
    rw [hleftENN, hf, hg] at h
    have hleft : 0 ≤ uniformProb (fun y : EdgeTuple V (k+1) =>
        Colorable q (G + tupleGraph (fun i : Fin k => y i.castSucc)) ∧
          ¬ FrozenPair q G (y (Fin.last k))) := uniformProb_nonneg _
    have hA : 0 ≤ uniformProb A := uniformProb_nonneg _
    have hB : 0 ≤ uniformProb B1 := uniformProb_nonneg _
    have ht := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal hleft, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB] at ht
    exact ht
  have hcontain : ∀ y : EdgeTuple V (k+1),
      Colorable q (G + tupleGraph y) →
        Colorable q (G + tupleGraph (fun i : Fin k => y i.castSucc)) ∧
        ¬ FrozenPair q G (y (Fin.last k)) := by
    intro y hy
    have hmono := (h9 V V q hq).1
    have hpref : subgraph (G + tupleGraph (fun i : Fin k => y i.castSucc))
        (G + tupleGraph y) := by
      intro e
      exact Nat.add_le_add_left (tupleGraph_mono_prefix y e) _
    have hcolorpref := (hmono _ _ hpref hy).1
    refine ⟨hcolorpref, ?_⟩
    intro hfreeze
    obtain ⟨u, v, huv, hfg⟩ := hfreeze
    have hkeep := (hmono _ _ (by intro e; exact Nat.le_add_right _ _) hy).2.1 u v hfg
    obtain ⟨σ, hσ⟩ := hy
    have hneq : σ u ≠ σ v := by
      have he : 0 < (G + tupleGraph y) (s(u,v)) := by
        rw [← huv]
        exact Nat.lt_of_lt_of_le (tupleGraph_contains_coordinate y (Fin.last k)) (Nat.le_add_left _ _)
      exact hσ u v he
    exact hneq (hkeep.2 σ hσ)
  have hprob := uniformProb_mono hcontain
  have hrec0 : uniformProb (fun y : EdgeTuple V (k+1) =>
      Colorable q (G + tupleGraph (fun i : Fin k => y i.castSucc)) ∧
        ¬ FrozenPair q G (y (Fin.last k))) =
      survival q G k * (1-kappa q G) := by
    rw [hfactorReal]
    change uniformProb A * uniformProb (fun y : Fin 1 → Pair V => B (y 0)) = _
    rw [uniformProb_fin1, uniformProb_not]
    rfl
  unfold survival
  calc
    uniformProb (fun y : EdgeTuple V (k+1) => Colorable q (G + tupleGraph y))
        ≤ uniformProb (fun y : EdgeTuple V (k+1) =>
          Colorable q (G + tupleGraph (fun i : Fin k => y i.castSucc)) ∧
            ¬ FrozenPair q G (y (Fin.last k))) := hprob
    _ = survival q G k * (1-kappa q G) := hrec0

private lemma pair_nonempty_of_card {V : Type u} [Fintype V] (hV : 2 ≤ Fintype.card V) :
    Nonempty (Pair V) := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega : 1 < Fintype.card V)
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  refine ⟨⟨s(u,v), ?_⟩⟩
  intro w hw
  rcases Sym2.eq_iff.mp hw with h | h
  · rcases h with ⟨huw, hvw⟩
    exact huv (huw.trans hvw.symm)
  · rcases h with ⟨huw, hvw⟩
    exact huv (huw.trans hvw.symm)

private lemma colorable_of_kappa_pos {V : Type u} [Fintype V] (q : ℕ)
    (hV : 2 ≤ Fintype.card V) (G : MGraph V) (hk : 0 < kappa q G) : Colorable q G := by
  classical
  letI : Nonempty (Pair V) := pair_nonempty_of_card hV
  by_contra hG
  have hsum : (∑ e : Pair V, indicator (FrozenPair q G e)) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have he' : ¬ FrozenPair q G e := by
      intro hf
      rcases hf with ⟨u, v, huv, hf⟩
      exact hG hf.1
    simp [indicator, he']
  have hzero : kappa q G = 0 := by
    unfold kappa uniformProb uniformMean
    rw [hsum]
    simp
  exact (ne_of_gt hk) hzero

private lemma geometric_lifetime_bound {V : Type u} [Fintype V]
    (h2 : ThLean.BP.S3.S3_02Statement.{u})
    (h9 : ThLean.BP.S3.S3_09bStatement.{u, u})
    (q : ℕ) (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V) (G : MGraph V)
    (hk : 0 < kappa q G) :
    (∀ k, survival q G k ≤ (1-kappa q G)^k) ∧
      lifetime q G ≠ ⊤ ∧ lifetimeReal q G ≤ 1 / kappa q G := by
  classical
  letI : Nonempty (Pair V) := pair_nonempty_of_card hV
  have hκrange := ((h9 V V q hq).2.2.2 G)
  have hr0 : 0 ≤ 1-kappa q G := by linarith [hκrange.2]
  have hr1 : 1-kappa q G < 1 := by linarith [hk]
  have hG : Colorable q G := colorable_of_kappa_pos q hV G hk
  have htuple : ∀ x : EdgeTuple V 0, tupleGraph x = 0 := by
    intro x
    ext e
    simp [tupleGraph]
  have hcolorZero : ∀ x : EdgeTuple V 0, Colorable q (G + tupleGraph x) := by
    intro x
    rw [htuple x, add_zero]
    exact hG
  have hzero : survival q G 0 = 1 := by
    simp [survival, uniformProb, uniformMean, indicator, hcolorZero]
  have hsurv : ∀ k, survival q G k ≤ (1-kappa q G)^k := by
    intro k
    induction k with
    | zero => simpa [hzero]
    | succ k ih =>
      have hs := survival_step h2 h9 q hq hV G k
      calc
        survival q G (k+1) ≤ survival q G k * (1-kappa q G) := hs
        _ ≤ (1-kappa q G)^k * (1-kappa q G) :=
          mul_le_mul_of_nonneg_right ih hr0
        _ = (1-kappa q G)^(k+1) := by rw [pow_succ]
  have hgeomSummable : Summable (fun k : ℕ => (1-kappa q G)^k) :=
    summable_geometric_of_lt_one hr0 hr1
  have hgeomENN : (∑' k : ℕ, ENNReal.ofReal ((1-kappa q G)^k)) =
      ENNReal.ofReal (1 / kappa q G) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun k : ℕ => (1-kappa q G)^k)
      (fun k => pow_nonneg hr0 k) hgeomSummable]
    rw [tsum_geometric_of_lt_one hr0 hr1]
    have hden : 1-(1-kappa q G) = kappa q G := by ring
    rw [hden]
    simp [one_div]
  have hbound : lifetime q G ≤ ENNReal.ofReal (1 / kappa q G) := by
    unfold lifetime
    calc
      (∑' k : ℕ, ENNReal.ofReal (survival q G k)) ≤
          ∑' k : ℕ, ENNReal.ofReal ((1-kappa q G)^k) :=
        ENNReal.tsum_le_tsum (fun k => ENNReal.ofReal_le_ofReal (hsurv k))
      _ = ENNReal.ofReal (1 / kappa q G) := hgeomENN
  have hfinite : lifetime q G ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)
  have hreal : lifetimeReal q G ≤ 1 / kappa q G := by
    unfold lifetimeReal
    calc
      (lifetime q G).toReal ≤ (ENNReal.ofReal (1 / kappa q G)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      _ = 1 / kappa q G := ENNReal.toReal_ofReal (one_div_nonneg.mpr hk.le)
  exact ⟨hsurv, hfinite, hreal⟩

theorem S3_27Statement_of_deps
    (h2 : ThLean.BP.S3.S3_02Statement.{u})
    (h9 : ThLean.BP.S3.S3_09bStatement.{u, u}) :
    ThLean.BP.S3.S3_27Statement.{u} := by
  intro V _ q hq hV
  refine ⟨?_, ?_⟩
  · intro G hk
    exact geometric_lifetime_bound h2 h9 q hq hV G hk
  · intro hN G
    have hκrange := ((h9 V V q hq).2.2.2 G)
    by_cases hk : 0 < kappa q G
    · have hlife := (geometric_lifetime_bound h2 h9 q hq hV G hk).2.2
      have hmul := mul_le_mul_of_nonneg_left hlife hk.le
      have hcancel : kappa q G * (1 / kappa q G) = 1 := by
        field_simp [ne_of_gt hk]
      nlinarith
    · have hκzero : kappa q G = 0 := le_antisymm (le_of_not_gt hk) hκrange.1
      simp [hκzero]

end ThLean.W.S329

example (h2 : ThLean.BP.S3.S3_02Statement.{u})
    (h9 : ThLean.BP.S3.S3_09bStatement.{u, u}) :
    ThLean.BP.S3.S3_27Statement.{u} :=
  ThLean.W.S329.S3_27Statement_of_deps h2 h9

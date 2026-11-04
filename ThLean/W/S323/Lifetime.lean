module

public import ThLean.BP.S3.Lifetime

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S323
open ThLean.BP.S3 ThresholdFoundations

private lemma pair_nonempty_of_card {V : Type u} [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  classical
  have hlt : 1 < Fintype.card V := by omega
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hlt
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hv
  have hrel := Sym2.exact hv
  cases hrel with
  | refl => exact hab rfl
  | swap => exact hab rfl

private lemma colorable_of_subgraph {V : Type u} [Fintype V]
    {q : ℕ} {G H : MGraph V} (hGH : subgraph G H)
    (hH : Colorable q H) : Colorable q G := by
  rcases hH with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro a b hab
  exact hσ a b (lt_of_lt_of_le hab (hGH (s(a, b))))

private lemma processGraph_mono {V : Type u} [Fintype V] (ω : EdgeStream V)
    {k l : ℕ} (h : k ≤ l) : subgraph (processGraph ω k) (processGraph ω l) := by
  intro e
  simp only [processGraph, tupleGraph]
  classical
  apply Finset.card_le_card_of_injOn (fun i : Fin k => Fin.castLE h i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa using hi
  · intro i hi j hj hij
    exact Fin.castLE_injective h hij

private lemma firstFailure_lt_iff_of_mono (P : ℕ → Prop)
    (hmono : ∀ i j, i ≤ j → P i → P j) (k : ℕ) :
    (k : WithTop ℕ) < firstFailure P ↔ ¬ P k := by
  classical
  by_cases h : ∃ m, P m
  ·
    simp only [firstFailure, dif_pos h, WithTop.coe_lt_coe]
    constructor
    · intro hk
      exact Nat.find_min h (WithTop.coe_lt_coe.mp hk)
    · intro hk
      by_contra hkn
      have hknat : ¬ k < Nat.find h := by
        intro hk'
        exact hkn (WithTop.coe_lt_coe.mpr hk')
      have hle : Nat.find h ≤ k := Nat.le_of_not_gt hknat
      exact hk (hmono (Nat.find h) k hle (Nat.find_spec h))
  · have hk : ¬ P k := fun hp => h ⟨k, hp⟩
    simp [firstFailure, h, hk]

private lemma firstFailure_eq_zero_of_zero (P : ℕ → Prop) (hP : P 0) :
    firstFailure P = 0 := by
  classical
  let hex : ∃ k, P k := ⟨0, hP⟩
  have hfind : Nat.find hex = 0 := (Nat.find_eq_zero hex).2 hP
  simp [firstFailure, hex, hfind]

private lemma noncolorable_add {V : Type u} [Fintype V] {q : ℕ}
    {G H : MGraph V} (hG : ¬ Colorable q G) : ¬ Colorable q (G + H) := by
  intro hsum
  apply hG
  apply colorable_of_subgraph
  · intro e
    exact Nat.le_add_right (G e) (H e)
  · exact hsum

private lemma uniformProb_bounds {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) : 0 ≤ uniformProb P ∧ uniformProb P ≤ 1 := by
  classical
  have hden : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  constructor
  · unfold uniformProb uniformMean
    apply div_nonneg
    · exact Finset.sum_nonneg fun a _ => by
        by_cases h : P a <;> simp [indicator, h]
    · positivity
  · unfold uniformProb uniformMean
    have hnum : (∑ a, indicator (P a)) ≤ (Fintype.card A : ℝ) := by
      calc
        (∑ a, indicator (P a)) ≤ ∑ _a : A, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          by_cases h : P a <;> simp [indicator, h]
        _ = (Fintype.card A : ℝ) := by simp
    rw [div_le_iff₀ hden]
    simpa using hnum

private lemma survival_bounds {V : Type u} [Fintype V]
    (hV : 2 ≤ Fintype.card V) (q : ℕ) (G : MGraph V) (k : ℕ) :
    0 ≤ survival q G k ∧ survival q G k ≤ 1 := by
  classical
  letI : Nonempty (Pair V) := pair_nonempty_of_card hV
  haveI : Nonempty (EdgeTuple V k) := inferInstance
  exact uniformProb_bounds (fun x : EdgeTuple V k => Colorable q (G + tupleGraph x))

private lemma tuplePrefix_eq_tupleGraph {V : Type u} [Fintype V] {b k : ℕ}
    (x : EdgeTuple V b) (hk : k ≤ b) :
    tuplePrefix x k = tupleGraph (fun i : Fin k => x (Fin.castLE hk i)) := by
  classical
  funext e
  simp only [tuplePrefix, tupleGraph]
  let s : Finset (Fin b) := Finset.univ.filter (fun i => i.val < k ∧ (x i).val = e)
  let t : Finset (Fin k) := Finset.univ.filter (fun i => (x (Fin.castLE hk i)).val = e)
  change s.card = t.card
  refine Finset.card_bij (s := s) (t := t)
    (fun i hi => (⟨i.val, by
      have hi' : i.val < k ∧ (x i).val = e := by simpa [s] using hi
      exact hi'.1⟩ : Fin k)) ?_ ?_ ?_
  · intro i hi
    have hi' : i.val < k ∧ (x i).val = e := by simpa [s] using hi
    have : (Fin.castLE hk (⟨i.val, hi'.1⟩ : Fin k)).val = i.val := rfl
    simpa [t, this] using hi'.2
  · intro i hi j hj h
    apply Fin.ext_iff.mpr
    simpa using congrArg (fun z : Fin k => z.val) h
  · intro j hj
    have hj' : (x (Fin.castLE hk j)).val = e := by simpa [t] using hj
    refine ⟨Fin.castLE hk j, ?_, ?_⟩
    · simpa [s, j.isLt]
    · rfl

private lemma survival_eq_prefix_mean {V : Type u} [Fintype V]
    (h02 : ThLean.BP.S3.S3_02Statement.{u})
    (hV : 2 ≤ Fintype.card V) (q : ℕ) (G : MGraph V)
    {k b : ℕ} (hk : k ≤ b) :
    survival q G k = uniformMean (fun x : EdgeTuple V b =>
      indicator (Colorable q (G + tuplePrefix x k))) := by
  classical
  letI : Nonempty (Pair V) := pair_nonempty_of_card hV
  let ι : Fin k ↪ Fin b := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  have hproj := (h02 (Pair V) b k ι).2.2.1
    (fun y : Fin k → Pair V => indicator (Colorable q (G + tupleGraph y)))
  change uniformMean (fun x : EdgeTuple V b =>
      indicator (Colorable q (G + tupleGraph (fun i : Fin k => x (ι i))))) =
    uniformMean (fun y : EdgeTuple V k =>
      indicator (Colorable q (G + tupleGraph y))) at hproj
  change uniformMean (fun y : EdgeTuple V k =>
      indicator (Colorable q (G + tupleGraph y))) =
    uniformMean (fun x : EdgeTuple V b =>
      indicator (Colorable q (G + tuplePrefix x k)))
  rw [← hproj]
  apply congrArg uniformMean
  funext x
  dsimp [ι]
  exact congrArg (fun H : MGraph V => indicator (Colorable q (G + H)))
    (tuplePrefix_eq_tupleGraph x hk).symm

private lemma finite_uniform_sum {A : Type*} [Fintype A]
    (b : ℕ) (f : ℕ → A → ℝ) :
    (∑ k ∈ Finset.range b, uniformMean (f k)) =
      uniformMean (fun a => ∑ k ∈ Finset.range b, f k a) := by
  classical
  unfold uniformMean
  change (∑ k ∈ Finset.range b, (∑ a ∈ Finset.univ, f k a) /
        (Fintype.card A : ℝ)) =
      ((∑ a ∈ Finset.univ, ∑ k ∈ Finset.range b, f k a) /
        (Fintype.card A : ℝ))
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]

theorem S3_21Statement_of_deps (h02 : ThLean.BP.S3.S3_02Statement.{u}) :
    ThLean.BP.S3.S3_21Statement.{u} := by
  classical
  intro V _ q hq hV
  letI : Nonempty (Pair V) := pair_nonempty_of_card hV
  have hsurv_nonneg : ∀ (G : MGraph V) k, 0 ≤ survival q G k :=
    fun G k => (survival_bounds hV q G k).1
  have hsurv_le_one : ∀ (G : MGraph V) k, survival q G k ≤ 1 :=
    fun G k => (survival_bounds hV q G k).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G ω k
    have hmono : ∀ i j, i ≤ j →
        (¬ Colorable q (G + processGraph ω i)) →
        ¬ Colorable q (G + processGraph ω j) := by
      intro i j hij hi
      intro hj
      apply hi
      apply colorable_of_subgraph
      · intro e
        exact Nat.add_le_add_left (processGraph_mono ω hij e) (G e)
      · exact hj
    simpa [freshHittingTime] using
      (firstFailure_lt_iff_of_mono
        (fun i => ¬ Colorable q (G + processGraph ω i)) hmono k)
  · intro G b
    calc
      truncatedLifetime q b G =
          ∑ k ∈ Finset.range b, survival q G k := rfl
      _ = ∑ k ∈ Finset.range b, uniformMean (fun x : EdgeTuple V b =>
            indicator (Colorable q (G + tuplePrefix x k))) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact survival_eq_prefix_mean h02 hV q G (Nat.le_of_lt (Finset.mem_range.mp hk))
      _ = uniformMean (fun x : EdgeTuple V b =>
            ∑ k ∈ Finset.range b,
              indicator (Colorable q (G + tuplePrefix x k))) := by
        apply finite_uniform_sum
  · intro G hG
    have hzero : ∀ k, survival q G k = 0 := by
      intro k
      have hbad : ∀ x : EdgeTuple V k, ¬ Colorable q (G + tupleGraph x) := by
        intro x
        exact noncolorable_add hG
      simp [survival, uniformProb, uniformMean, indicator, hbad]
    refine ⟨?_, ?_, ?_⟩
    · simp [lifetime, hzero]
    · intro b
      simp [truncatedLifetime, hzero]
    · intro ω
      have hP : ¬ Colorable q (G + processGraph ω 0) := by
        exact noncolorable_add (G := G) (H := processGraph ω 0) hG
      change firstFailure (fun k => ¬ Colorable q (G + processGraph ω k)) = 0
      exact firstFailure_eq_zero_of_zero _ hP
  · intro G b
    have hnonneg := fun k => hsurv_nonneg G k
    have hle := fun k => hsurv_le_one G k
    refine ⟨?_, ?_, ?_⟩
    · unfold truncatedLifetime
      exact Finset.sum_nonneg fun k hk => hnonneg k
    · unfold truncatedLifetime
      calc
        (∑ k ∈ Finset.range b, survival q G k) ≤
            ∑ _k ∈ Finset.range b, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hle k
        _ = b := by simp
    · change ENNReal.ofReal (truncatedLifetime q b G) ≤ lifetime q G
      rw [truncatedLifetime, lifetime]
      calc
        ENNReal.ofReal (∑ k ∈ Finset.range b, survival q G k) =
            ∑ k ∈ Finset.range b, ENNReal.ofReal (survival q G k) :=
          ENNReal.ofReal_sum_of_nonneg (fun k hk => hnonneg k)
        _ ≤ ∑' k : ℕ, ENNReal.ofReal (survival q G k) :=
          ENNReal.sum_le_tsum (Finset.range b)
  · intro G hG
    have hs0 : survival q G 0 = 1 := by
      have hgraph : ∀ x : EdgeTuple V 0, tupleGraph x = 0 := by
        intro x
        funext e
        simp [tupleGraph]
      have hall : ∀ x : EdgeTuple V 0, Colorable q (G + tupleGraph x) := by
        intro x
        rw [hgraph x, add_zero]
        exact hG
      simp [survival, uniformProb, uniformMean, indicator, hall]
    refine ⟨?_, ?_⟩
    · intro b hb
      unfold truncatedLifetime
      calc
        (1 : ℝ) = survival q G 0 := hs0.symm
        _ ≤ ∑ k ∈ Finset.range b, survival q G k := by
          apply Finset.single_le_sum
          · intro k hk
            exact hsurv_nonneg G k
          · simp only [Finset.mem_range]
            omega
    · change (1 : ℝ≥0∞) ≤ lifetime q G
      rw [lifetime]
      calc
        (1 : ℝ≥0∞) = ENNReal.ofReal (survival q G 0) := by simp [hs0]
        _ ≤ ∑' k : ℕ, ENNReal.ofReal (survival q G k) :=
          ENNReal.le_tsum (f := fun k : ℕ => ENNReal.ofReal (survival q G k)) 0
  · intro G
    constructor
    · intro b b' hbb'
      unfold truncatedLifetime
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hbb')
        (fun k hk hnot => hsurv_nonneg G k)
    · simp [truncatedLifetime]

end ThLean.W.S323

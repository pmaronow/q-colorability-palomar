import ThLean.W.S539.S5_30_Prelim

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S539
open ThresholdFoundations ThLean.BP.S5

variable {V : Type*} [Fintype V]

private lemma indicator_bounds (P : Prop) : 0 ≤ indicator P ∧ indicator P ≤ 1 := by
  unfold indicator
  by_cases h : P <;> simp [h]

private lemma lowKappa_bounds (q D : ℕ) (hV : 2 ≤ Fintype.card V) (G : MGraph V) :
    0 ≤ lowKappa q D G ∧ lowKappa q D G ≤ 1 := by
  classical
  have hpairNat : 0 < Fintype.card (Pair V) := by
    rw [pair_card]
    exact Nat.choose_pos (by omega)
  have hpair : 0 < (Fintype.card (Pair V) : ℝ) := by exact_mod_cast hpairNat
  have hsum0 : 0 ≤ ∑ e : Pair V, indicator (FrozenPair q G e ∧ lowEdge G D e) :=
    Finset.sum_nonneg (fun e _ => (indicator_bounds _).1)
  have hsum_le :
      (∑ e : Pair V, indicator (FrozenPair q G e ∧ lowEdge G D e)) ≤
        (Fintype.card (Pair V) : ℝ) := by
    calc
      _ ≤ ∑ _e : Pair V, (1 : ℝ) :=
        Finset.sum_le_sum (fun e _ => (indicator_bounds _).2)
      _ = (Fintype.card (Pair V) : ℝ) := by simp
  unfold lowKappa kappaKind uniformProb uniformMean
  constructor
  · exact div_nonneg hsum0 (le_of_lt hpair)
  · calc
      _ ≤ (Fintype.card (Pair V) : ℝ) / (Fintype.card (Pair V) : ℝ) :=
        div_le_div_of_nonneg_right hsum_le (le_of_lt hpair)
      _ = 1 := div_self (ne_of_gt hpair)

private lemma partnerCount_le_card (q : ℕ) (G : MGraph V) (a : V) :
    partnerCount q G a ≤ Fintype.card V := by
  unfold partnerCount frozenPartnerCount
  calc
    (Finset.univ.filter (fun v => v ≠ a ∧ Frozen q G a v)).card ≤ Finset.univ.card :=
      Finset.card_filter_le _ _
    _ = Fintype.card V := Finset.card_univ

private lemma lowRootTerm_bounds (q D : ℕ) (f : MGraph V → ℝ)
    (hf : ∀ G, 0 ≤ f G ∧ f G ≤ 1) (a : V) (G : MGraph V) :
    0 ≤ lowRootTerm q D f a G ∧ lowRootTerm q D f a G ≤ Fintype.card V := by
  unfold lowRootTerm
  have hi := indicator_bounds (degree G a ≤ D)
  have hp0 : 0 ≤ (partnerCount q G a : ℝ) := Nat.cast_nonneg _
  have hp1 : (partnerCount q G a : ℝ) ≤ Fintype.card V := by
    exact_mod_cast partnerCount_le_card q G a
  have hfG := hf G
  constructor
  · exact mul_nonneg (mul_nonneg hi.1 hp0) hfG.1
  · have h1 : indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) ≤
        (1 : ℝ) * (partnerCount q G a : ℝ) := mul_le_mul_of_nonneg_right hi.2 hp0
    have h2 : (1 : ℝ) * (partnerCount q G a : ℝ) ≤
        (1 : ℝ) * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_left hp1 (by norm_num)
    calc
        indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) * f G ≤
            (1 : ℝ) * (partnerCount q G a : ℝ) * f G :=
          mul_le_mul_of_nonneg_right h1 hfG.1
        _ ≤ (1 : ℝ) * (Fintype.card V : ℝ) * f G :=
          mul_le_mul_of_nonneg_right h2 hfG.1
        _ ≤ (1 : ℝ) * (Fintype.card V : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hfG.2 (by positivity)
        _ = Fintype.card V := by ring

private lemma lowKappa_le_rootSum (q D : ℕ) (hV : 2 ≤ Fintype.card V)
    (G : MGraph V) :
    lowKappa q D G ≤
      (1 / ((Fintype.card V).choose 2 : ℝ)) *
        ∑ a : V, indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) := by
  classical
  letI : Fintype (Σ a : V, {v : V // v ≠ a ∧ Frozen q G a v ∧ degree G a ≤ D}) := inferInstance
  letI : Fintype (lowIncidences q D G) := by
    unfold lowIncidences
    infer_instance
  have hcard := lowPair_card_le_incidence_card q D G
  have hreal :
      (Fintype.card {e : Pair V // FrozenPair q G e ∧ lowEdge G D e} : ℝ) ≤
        (Fintype.card (lowIncidences q D G) : ℝ) := by exact_mod_cast hcard
  rw [lowPair_card, lowIncidence_card] at hreal
  have hpairNat : 0 < Fintype.card (Pair V) := by
    rw [pair_card]
    exact Nat.choose_pos (by omega)
  have hpair : 0 < (Fintype.card (Pair V) : ℝ) := by exact_mod_cast hpairNat
  have hratio := div_le_div_of_nonneg_right hreal (le_of_lt hpair)
  have hratio' :
      (∑ e : Pair V, indicator (FrozenPair q G e ∧ lowEdge G D e)) /
          (Fintype.card (Pair V) : ℝ) ≤
        (∑ a : V, indicator (degree G a ≤ D) * (partnerCount q G a : ℝ)) /
          (Fintype.card (Pair V) : ℝ) := hratio
  unfold lowKappa kappaKind uniformProb uniformMean
  rw [pair_card]
  calc
    _ ≤ (∑ a : V, indicator (degree G a ≤ D) * (partnerCount q G a : ℝ)) /
          ((Fintype.card V).choose 2 : ℝ) := by
            simpa [pair_card] using hratio'
    _ = (1 / ((Fintype.card V).choose 2 : ℝ)) *
          ∑ a : V, indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) := by ring

private lemma lawMean_finset_sum {ν : PMF (MGraph V)}
    (g : V → MGraph V → ℝ)
    (hg : ∀ a, Summable (fun G => (ν G).toReal * g a G)) :
    lawMean ν (fun G => ∑ a : V, g a G) = ∑ a : V, lawMean ν (g a) := by
  unfold lawMean
  have hs :
      ∑' G, (ν G).toReal * (∑ a : V, g a G) =
        ∑' G, ∑ a : V, (ν G).toReal * g a G := by
    apply tsum_congr
    intro G
    rw [Finset.mul_sum]
  rw [hs]
  exact Summable.tsum_finsetSum (s := Finset.univ) (f := fun a G => (ν G).toReal * g a G)
    (fun a ha => hg a)

private lemma lowRootMean_eq {ν : PMF (MGraph V)} (f : MGraph V → ℝ)
    (hfi : relabelInvariant f) (hν : invariantLaw ν) (q D : ℕ)
    (a b : V) :
    lawMean ν (lowRootTerm q D f a) = lawMean ν (lowRootTerm q D f b) := by
  let π : Equiv.Perm V := Equiv.swap a b
  have hπ : π a = b := Equiv.swap_apply_left a b
  have hpt (G : MGraph V) :
      lowRootTerm q D f b (relabel π G) = lowRootTerm q D f a G := by
    simpa [hπ] using lowRootTerm_relabel π q D f hfi G a
  have hrel := lawMean_relabel π (hν π) (lowRootTerm q D f b)
  calc
    lawMean ν (lowRootTerm q D f a) = lawMean ν (lowRootTerm q D f b) := by
      symm
      calc
        lawMean ν (lowRootTerm q D f b) =
            lawMean ν (fun G => lowRootTerm q D f b (relabel π G)) := hrel
        _ = lawMean ν (lowRootTerm q D f a) := by
          congr 1
          funext G
          exact hpt G

private lemma choose_two_factor (n : ℕ) (hn : 2 ≤ n) :
    (1 / (n.choose 2 : ℝ)) * n = 2 / ((n : ℝ) - 1) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [Nat.cast_choose_two]
  field_simp

theorem S5_30Statement_holds : ThLean.BP.S5.S5_30Statement := by
  classical
  intro V inst q hq hV D
  constructor
  · intro G
    exact lowKappa_le_rootSum q D hV G
  · intro ν hν f hfi hf a
    let n : ℝ := Fintype.card V
    let c : ℝ := 1 / ((Fintype.card V).choose 2 : ℝ)
    have hc0 : 0 ≤ c := by
      dsimp [c]
      apply div_nonneg (by norm_num)
      positivity
    have hLowBound : ∀ G, 0 ≤ lowKappa q D G * f G ∧ lowKappa q D G * f G ≤ 1 := by
      intro G
      have hκ := lowKappa_bounds q D hV G
      constructor
      · exact mul_nonneg hκ.1 (hf G).1
      · calc
          lowKappa q D G * f G ≤ 1 * f G := mul_le_mul_of_nonneg_right hκ.2 (hf G).1
          _ ≤ 1 := by simpa using (hf G).2
    have hLowSummable := lawMean_summable_of_bounded (ν := ν) (hC := by norm_num)
      hLowBound
    have hRootBound (x : V) (G : MGraph V) :
        0 ≤ lowRootTerm q D f x G ∧ lowRootTerm q D f x G ≤ Fintype.card V :=
      lowRootTerm_bounds q D f hf x G
    have hRootSummable (x : V) :
        Summable (fun G => (ν G).toReal * lowRootTerm q D f x G) := by
      apply lawMean_summable_of_bounded (ν := ν) (C := Fintype.card V)
      · exact_mod_cast Nat.cast_nonneg (Fintype.card V)
      · intro G
        exact hRootBound x G
    have hSumBound (G : MGraph V) :
        0 ≤ (∑ x : V, lowRootTerm q D f x G) ∧
          (∑ x : V, lowRootTerm q D f x G) ≤
            (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
      constructor
      · exact Finset.sum_nonneg (fun x _ => (hRootBound x G).1)
      · calc
          _ ≤ ∑ _x : V, (Fintype.card V : ℝ) :=
            Finset.sum_le_sum (fun x _ => (hRootBound x G).2)
          _ = (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by simp
    have hWeightedSumBound (G : MGraph V) :
        0 ≤ c * (∑ x : V, lowRootTerm q D f x G) ∧
          c * (∑ x : V, lowRootTerm q D f x G) ≤
            c * ((Fintype.card V : ℝ) * (Fintype.card V : ℝ)) := by
      exact ⟨mul_nonneg hc0 (hSumBound G).1,
        mul_le_mul_of_nonneg_left (hSumBound G).2 hc0⟩
    have hRightSummable := lawMean_summable_of_bounded (ν := ν)
      (C := c * ((Fintype.card V : ℝ) * (Fintype.card V : ℝ)))
      (mul_nonneg hc0 (mul_nonneg (by exact_mod_cast Nat.cast_nonneg (Fintype.card V))
        (by exact_mod_cast Nat.cast_nonneg (Fintype.card V))))
      hWeightedSumBound
    have hBaseSummable := lawMean_summable_of_bounded (ν := ν)
      (C := (Fintype.card V : ℝ) * (Fintype.card V : ℝ))
      (mul_nonneg (by exact_mod_cast Nat.cast_nonneg (Fintype.card V))
        (by exact_mod_cast Nat.cast_nonneg (Fintype.card V)))
      hSumBound
    have hfactor :
        lawMean ν (fun G => c * (∑ x : V, lowRootTerm q D f x G)) =
          c * lawMean ν (fun G => ∑ x : V, lowRootTerm q D f x G) := by
      unfold lawMean
      have ht := hBaseSummable.tsum_mul_left c
      calc
        (∑' G, (ν G).toReal * (c * (∑ x : V, lowRootTerm q D f x G))) =
            ∑' G, c * ((ν G).toReal * (∑ x : V, lowRootTerm q D f x G)) := by
              apply tsum_congr
              intro G
              ring
        _ = c * ∑' G, (ν G).toReal * (∑ x : V, lowRootTerm q D f x G) := ht
    have hpoint (G : MGraph V) :
        lowKappa q D G * f G ≤ c * (∑ x : V, lowRootTerm q D f x G) := by
      have hbase := lowKappa_le_rootSum q D hV G
      calc
        lowKappa q D G * f G ≤
            ((1 / ((Fintype.card V).choose 2 : ℝ)) *
              ∑ x : V, indicator (degree G x ≤ D) * (partnerCount q G x : ℝ)) * f G :=
          mul_le_mul_of_nonneg_right hbase (hf G).1
        _ = c * (∑ x : V, lowRootTerm q D f x G) := by
          dsimp [c]
          unfold lowRootTerm
          rw [← Finset.sum_mul]
          ring
    have hcmp :
        lawMean ν (fun G => lowKappa q D G * f G) ≤
          lawMean ν (fun G => c * (∑ x : V, lowRootTerm q D f x G)) := by
      unfold lawMean
      apply Summable.tsum_le_tsum
      · intro G
        exact mul_le_mul_of_nonneg_left (hpoint G) ENNReal.toReal_nonneg
      · exact hLowSummable
      · exact hRightSummable
    have hsumMean := lawMean_finset_sum (ν := ν)
      (g := lowRootTerm q D f) hRootSummable
    have hrootEq :
        (∑ x : V, lawMean ν (lowRootTerm q D f x)) =
          (Fintype.card V : ℝ) * lawMean ν (lowRootTerm q D f a) := by
      calc
        _ = ∑ x : V, lawMean ν (lowRootTerm q D f a) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact lowRootMean_eq f hfi hν q D x a
        _ = (Fintype.card V : ℝ) * lawMean ν (lowRootTerm q D f a) := by simp
    have hcoef := choose_two_factor (Fintype.card V) hV
    refine ⟨?_, ?_, ?_⟩
    · simpa [lowRootTerm] using hLowSummable
    · simpa [lowRootTerm] using hRootSummable a
    · calc
        lawMean ν (fun G => lowKappa q D G * f G) ≤
            lawMean ν (fun G => c * (∑ x : V, lowRootTerm q D f x G)) := hcmp
        _ = c * (∑ x : V, lawMean ν (lowRootTerm q D f x)) := by rw [hfactor, hsumMean]
        _ = c * ((Fintype.card V : ℝ) * lawMean ν (lowRootTerm q D f a)) := by rw [hrootEq]
        _ = (2 / ((Fintype.card V : ℝ) - 1)) *
              lawMean ν (lowRootTerm q D f a) := by
          dsimp [c]
          calc
            (1 / ((Fintype.card V).choose 2 : ℝ)) *
                ((Fintype.card V : ℝ) * lawMean ν (lowRootTerm q D f a)) =
              ((1 / ((Fintype.card V).choose 2 : ℝ)) * (Fintype.card V : ℝ)) *
                lawMean ν (lowRootTerm q D f a) := by ring
            _ = (2 / ((Fintype.card V : ℝ) - 1)) *
                lawMean ν (lowRootTerm q D f a) := by rw [hcoef]

example : ThLean.BP.S5.S5_30Statement := S5_30Statement_holds

end ThLean.W.S539

module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S374
open ThresholdFoundations
open ThLean.BP.S3
universe u

private theorem indicator_nonneg_local (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split <;> norm_num

private theorem witness_prob_bound
    {V : Type u} [Fintype V] (h03 : S3_03aStatement.{u})
    (h68 : S3_68Statement.{u}) (h70 : S3_70Statement.{u})
    (k m : ℕ) (hk : 2 ≤ k) (hkn : k ≤ Fintype.card V) :
    uniformProb (fun x : EdgeTuple V m =>
      ∃ G : {G : MGraph V // Witness k G}, subgraph G.1 (tupleGraph x)) ≤
      2 * ((k+2 : ℕ) : ℝ)^2 * (Fintype.card V : ℝ)^k *
        ((m : ℝ) / ((Fintype.card V).choose 2 : ℝ))^(k+1) := by
  classical
  let W : Set (MGraph V) := {G | Witness k G}
  have hWfinite : W.Finite := by
    simpa [W] using (h68 V k hk hkn).1
  letI : Fintype W := hWfinite.fintype
  have hWcard : Fintype.card W ≤
      2 * (k+2)^2 * (Fintype.card V)^k := by
    rw [Set.fintypeCard_eq_ncard]
    simpa [W] using (h68 V k hk hkn).2.1
  have hpair := (h03 V (by omega : 2 ≤ Fintype.card V)).1
  have hnum : (Fintype.card W : ℝ) ≤
      2 * ((k+2 : ℕ) : ℝ)^2 * (Fintype.card V : ℝ)^k := by
    calc
      (Fintype.card W : ℝ) ≤
          ((2 * (k+2)^2 * (Fintype.card V)^k : ℕ) : ℝ) := by exact_mod_cast hWcard
      _ = 2 * ((k+2 : ℕ) : ℝ)^2 * (Fintype.card V : ℝ)^k := by push_cast; ring
  have hp_nonneg : 0 ≤ (m : ℝ) / ((Fintype.card V).choose 2 : ℝ) := by
    positivity
  have h_union :
      uniformProb (fun x : EdgeTuple V m =>
        ∃ G : W, subgraph G.1 (tupleGraph x)) ≤
        ∑ G : W,
          graphProb m (fun H => subgraph G.1 H) := by
    unfold uniformProb uniformMean graphProb
    have hpnt (x : EdgeTuple V m) :
        indicator (∃ G : W, subgraph G.1 (tupleGraph x)) ≤
          ∑ G : W, indicator (subgraph G.1 (tupleGraph x)) := by
      by_cases hex : ∃ G : W, subgraph G.1 (tupleGraph x)
      · obtain ⟨G, hG⟩ := hex
        have hterm : indicator (subgraph G.1 (tupleGraph x)) = 1 := by
          simp [indicator, hG]
        have htop : indicator (∃ G : W,
            subgraph G.1 (tupleGraph x)) = 1 := by
          unfold indicator
          rw [if_pos (show ∃ G : W, subgraph G.1 (tupleGraph x) from ⟨G, hG⟩)]
        calc
          indicator (∃ G' : W,
              subgraph G'.1 (tupleGraph x)) = 1 := htop
          _ = indicator (subgraph G.1 (tupleGraph x)) := hterm.symm
          _ ≤ ∑ G' : W,
              indicator (subgraph G'.1 (tupleGraph x)) :=
            Finset.single_le_sum
              (f := fun G' : W => indicator (subgraph G'.1 (tupleGraph x)))
              (fun G' _ => indicator_nonneg_local _)
              (Finset.mem_univ G)
      · rw [show indicator (∃ G : W,
            subgraph G.1 (tupleGraph x)) = 0 by simp [indicator, hex]]
        apply Finset.sum_nonneg
        intro G _
        exact indicator_nonneg_local _
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpnt x)
    have hden : 0 ≤ (Fintype.card (EdgeTuple V m) : ℝ) := by positivity
    calc
      (∑ x : EdgeTuple V m,
          indicator (∃ G : W, subgraph G.1 (tupleGraph x))) /
          (Fintype.card (EdgeTuple V m) : ℝ) ≤
        (∑ x : EdgeTuple V m,
          ∑ G : W, indicator (subgraph G.1 (tupleGraph x))) /
          (Fintype.card (EdgeTuple V m) : ℝ) := div_le_div_of_nonneg_right hsum hden
      _ = ∑ G : W,
          (∑ x : EdgeTuple V m, indicator (subgraph G.1 (tupleGraph x))) /
            (Fintype.card (EdgeTuple V m) : ℝ) := by
          simp_rw [Finset.sum_div]
          change
            (∑ x ∈ (Finset.univ : Finset (EdgeTuple V m)),
              ∑ G ∈ (Finset.univ : Finset W),
                indicator (subgraph G.1 (tupleGraph x)) /
                  (Fintype.card (EdgeTuple V m) : ℝ)) =
            ∑ G ∈ (Finset.univ : Finset W),
              ∑ x ∈ (Finset.univ : Finset (EdgeTuple V m)),
                indicator (subgraph G.1 (tupleGraph x)) /
                  (Fintype.card (EdgeTuple V m) : ℝ)
          rw [Finset.sum_comm]
      _ = ∑ G : W,
          graphProb m (fun H => subgraph G.1 H) := by
          simp [graphProb, uniformProb, uniformMean]
  have hsumprob :
      (∑ G : W,
          graphProb m (fun H => subgraph G.1 H)) ≤
        ∑ G : W,
          ((m : ℝ) / ((Fintype.card V).choose 2 : ℝ))^(k+1) := by
    apply Finset.sum_le_sum
    intro G _
    have hprob := h70 V (by omega : 2 ≤ Fintype.card V) G.1 m G.2.1
    have hedge := (h68 V k hk hkn).2.2 G.1 G.2
    rw [hedge, hpair] at hprob
    exact hprob
  have hconstant :
      (∑ G : W,
          ((m : ℝ) / ((Fintype.card V).choose 2 : ℝ))^(k+1)) =
        (Fintype.card W : ℝ) *
          ((m : ℝ) / ((Fintype.card V).choose 2 : ℝ))^(k+1) := by
    simp
  calc
    uniformProb (fun x : EdgeTuple V m =>
      ∃ G : W, subgraph G.1 (tupleGraph x)) ≤
        ∑ G : W, graphProb m (fun H => subgraph G.1 H) := h_union
    _ ≤ ∑ G : W,
          ((m : ℝ) / ((Fintype.card V).choose 2 : ℝ))^(k+1) := hsumprob
    _ = (Fintype.card W : ℝ) *
          ((m : ℝ) / ((Fintype.card V).choose 2 : ℝ))^(k+1) := hconstant
    _ ≤ (2 * ((k+2 : ℕ) : ℝ)^2 * (Fintype.card V : ℝ)^k) *
          ((m : ℝ) / ((Fintype.card V).choose 2 : ℝ))^(k+1) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 2 * ((k+2 : ℕ) : ℝ)^2 * (Fintype.card V : ℝ)^k *
          ((m : ℝ) / ((Fintype.card V).choose 2 : ℝ))^(k+1) := by ring

theorem S3_71Statement_of_deps
    (h03 : S3_03aStatement.{u}) (h65 : S3_65Statement.{u})
    (h68 : S3_68Statement.{u}) (h70 : S3_70Statement.{u}) :
    S3_71Statement.{u} := by
  classical
  intro V _ q hq hV m
  have hpair := (h03 V hV).1
  have hpairpos := (h03 V hV).2.1
  have hsurv : processSurvival (V := V) q m =
      uniformProb (fun x : EdgeTuple V m => Colorable q (tupleGraph x)) := by
    simp [processSurvival, survival, uniformProb, uniformMean, zero_add]
  have hcomp : 1 - processSurvival (V := V) q m =
      uniformProb (fun x : EdgeTuple V m => ¬ Colorable q (tupleGraph x)) := by
    rw [hsurv]
    have hcardpos : 0 < (Fintype.card (EdgeTuple V m) : ℝ) := by
      have hpaircard : 0 < Fintype.card (Pair V) := hpairpos
      have hpairNE : Nonempty (Pair V) := Fintype.card_pos_iff.mp hpaircard
      have htuple : Nonempty (EdgeTuple V m) := by
        exact ⟨fun _ => Classical.choice hpairNE⟩
      exact_mod_cast (Fintype.card_pos_iff.mpr htuple)
    unfold uniformProb uniformMean
    have hsum :
        (∑ x : EdgeTuple V m, indicator (Colorable q (tupleGraph x))) +
          (∑ x : EdgeTuple V m, indicator (¬ Colorable q (tupleGraph x))) =
            (Fintype.card (EdgeTuple V m) : ℝ) := by
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ _x : EdgeTuple V m, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hc : Colorable q (tupleGraph x) <;> simp [indicator, hc]
        _ = _ := by simp
    field_simp [ne_of_gt hcardpos]
    linarith
  let N := Fintype.card V
  have hbadpoint (x : EdgeTuple V m) :
      indicator (¬ Colorable q (tupleGraph x)) ≤
        ∑ k ∈ Finset.Icc 2 N,
          indicator (∃ G : {G : MGraph V // Witness k G}, subgraph G.1 (tupleGraph x)) := by
    by_cases hbad : ¬ Colorable q (tupleGraph x)
    · obtain ⟨k, F, hk, hkn, hsub, hW, hedge⟩ := h65 V q hq hV
        (tupleGraph x) (by
          intro v
          unfold tupleGraph
          apply Finset.card_eq_zero.mpr
          apply Finset.filter_eq_empty_iff.mpr
          intro i hi
          exact (x i).property v) hbad
      have hkmem : k ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨hk, hkn⟩
      have hsingle :
          indicator (∃ G : {G : MGraph V // Witness k G}, subgraph G.1 (tupleGraph x)) ≤
            ∑ j ∈ Finset.Icc 2 N,
              indicator (∃ G : {G : MGraph V // Witness j G}, subgraph G.1 (tupleGraph x)) := by
        let f : ℕ → ℝ := fun j => indicator
          (∃ G : {G : MGraph V // Witness j G}, subgraph G.1 (tupleGraph x))
        change f k ≤ ∑ j ∈ Finset.Icc 2 N, f j
        exact Finset.single_le_sum (s := Finset.Icc 2 N) (f := f)
          (fun j hj => indicator_nonneg_local _) hkmem
      have hterm : indicator (∃ G : {G : MGraph V // Witness k G},
          subgraph G.1 (tupleGraph x)) = 1 := by
        unfold indicator
        have hF : Witness k F := hW
        rw [if_pos (show ∃ G : {G : MGraph V // Witness k G},
          subgraph G.1 (tupleGraph x) from ⟨⟨F, hF⟩, hsub⟩)]
      rw [show indicator (¬ Colorable q (tupleGraph x)) = 1 by simp [indicator, hbad]]
      exact le_trans (le_of_eq hterm.symm) hsingle
    · simp [indicator, hbad]
  have hbadprob :
      uniformProb (fun x : EdgeTuple V m => ¬ Colorable q (tupleGraph x)) ≤
        ∑ k ∈ Finset.Icc 2 N,
          uniformProb (fun x : EdgeTuple V m =>
            ∃ G : {G : MGraph V // Witness k G}, subgraph G.1 (tupleGraph x)) := by
    unfold uniformProb uniformMean
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hbadpoint x)
    have hden : 0 ≤ (Fintype.card (EdgeTuple V m) : ℝ) := by positivity
    calc
      (∑ x : EdgeTuple V m, indicator (¬ Colorable q (tupleGraph x))) /
          (Fintype.card (EdgeTuple V m) : ℝ) ≤
        (∑ x : EdgeTuple V m,
          ∑ k ∈ Finset.Icc 2 N,
            indicator (∃ G : {G : MGraph V // Witness k G}, subgraph G.1 (tupleGraph x))) /
          (Fintype.card (EdgeTuple V m) : ℝ) := div_le_div_of_nonneg_right hsum hden
      _ = ∑ k ∈ Finset.Icc 2 N,
            (∑ x : EdgeTuple V m,
              indicator (∃ G : {G : MGraph V // Witness k G}, subgraph G.1 (tupleGraph x))) /
              (Fintype.card (EdgeTuple V m) : ℝ) := by
          simp_rw [Finset.sum_div]
          change
            (∑ x ∈ (Finset.univ : Finset (EdgeTuple V m)),
              ∑ k ∈ Finset.Icc 2 N,
                indicator (∃ G : {G : MGraph V // Witness k G},
                  subgraph G.1 (tupleGraph x)) /
                  (Fintype.card (EdgeTuple V m) : ℝ)) =
            ∑ k ∈ Finset.Icc 2 N,
              ∑ x ∈ (Finset.univ : Finset (EdgeTuple V m)),
                indicator (∃ G : {G : MGraph V // Witness k G},
                  subgraph G.1 (tupleGraph x)) /
                  (Fintype.card (EdgeTuple V m) : ℝ)
          rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.Icc 2 N,
            uniformProb (fun x : EdgeTuple V m =>
              ∃ G : {G : MGraph V // Witness k G}, subgraph G.1 (tupleGraph x)) := by
          simp [uniformProb, uniformMean]
  have hsumfinal :
      (∑ k ∈ Finset.Icc 2 N,
          uniformProb (fun x : EdgeTuple V m =>
            ∃ G : {G : MGraph V // Witness k G}, subgraph G.1 (tupleGraph x))) ≤
        ∑ k ∈ Finset.Icc 2 N,
          2 * ((k+2 : ℕ) : ℝ)^2 * (N : ℝ)^k *
            ((m : ℝ) / (N.choose 2 : ℝ))^(k+1) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    simpa [N] using witness_prob_bound h03 h68 h70 k m hk'.1 hk'.2
  rw [hcomp]
  exact le_trans hbadprob hsumfinal

example (h03 : S3_03aStatement.{u}) (h65 : S3_65Statement.{u})
    (h68 : S3_68Statement.{u}) (h70 : S3_70Statement.{u}) :
    S3_71Statement.{u} := S3_71Statement_of_deps h03 h65 h68 h70

end ThLean.W.S374

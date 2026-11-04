module

public import ThLean.W.S303.Graph

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.W.S303
open ThLean.BP.S3 ThresholdFoundations

private theorem touchCount_distributionENN {V : Type u} [Fintype V]
    (h02 : ThLean.BP.S3.S3_02Statement.{u})
    (h03a : ThLean.BP.S3.S3_03aStatement.{u})
    (hn : 2 ≤ Fintype.card V) (a : V) :
    ∀ (m k : ℕ),
      uniformMeanENN (fun x : EdgeTuple V m =>
        if touchCount a x = k then (1 : ℝ≥0∞) else 0) =
        ENNReal.ofReal (binomialWeight m (2 / Fintype.card V) k) := by
  have hpairPos : 0 < Fintype.card (Pair V) := (h03a V hn).2.1
  letI : Nonempty (Pair V) := Fintype.card_pos_iff.mp hpairPos
  let p : ℝ := 2 / Fintype.card V
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ 1-p := by
    dsimp [p]
    have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    have hcardR : (0 : ℝ) < Fintype.card V := by positivity
    rw [sub_nonneg, div_le_iff₀ hcardR]
    simpa using hnR
  intro m
  induction m with
  | zero =>
      intro k
      by_cases hk : k = 0
      · subst k
        simp [uniformMeanENN, touchCount, binomialWeight, p]
      · simp [uniformMeanENN, touchCount, binomialWeight, p, hk]
        exact fun h => hk h.symm
  | succ m ih =>
      intro k
      let f0 : (Fin m → Pair V) → ℝ≥0∞ := fun x =>
        if touchCount a x = k then 1 else 0
      let f1 : (Fin m → Pair V) → ℝ≥0∞ := fun x =>
        if touchCount a x + 1 = k then 1 else 0
      let g0 : Pair V → ℝ≥0∞ := fun e =>
        @ite ℝ≥0∞ (¬ Touches a e.val)
          (Classical.propDecidable (¬ Touches a e.val)) 1 0
      let g1 : Pair V → ℝ≥0∞ := fun e =>
        if Touches a e.val then 1 else 0
      have hsplit (x : EdgeTuple V (m+1)) :
          (if touchCount a x = k then (1 : ℝ≥0∞) else 0) =
            f0 (fun i => x i.castSucc) * g0 (x (Fin.last m)) +
              f1 (fun i => x i.castSucc) * g1 (x (Fin.last m)) := by
        by_cases ht : Touches a (x (Fin.last m)).val
        · simp [touchCount_snoc, ht, f0, f1, g0, g1]
        · simp [touchCount_snoc, ht, f0, f1, g0, g1]
      have hdecomp :
          uniformMeanENN (fun x : EdgeTuple V (m+1) =>
            if touchCount a x = k then (1 : ℝ≥0∞) else 0) =
            uniformMeanENN (fun x : EdgeTuple V (m+1) =>
              f0 (fun i => x i.castSucc) * g0 (x (Fin.last m))) +
            uniformMeanENN (fun x : EdgeTuple V (m+1) =>
              f1 (fun i => x i.castSucc) * g1 (x (Fin.last m))) := by
        calc
          _ = uniformMeanENN (fun x : EdgeTuple V (m+1) =>
              f0 (fun i => x i.castSucc) * g0 (x (Fin.last m)) +
                f1 (fun i => x i.castSucc) * g1 (x (Fin.last m))) := by
                  congr 1
                  funext x
                  exact hsplit x
          _ = _ := uniformMeanENN_add _ _
      rw [hdecomp]
      have hprob := touches_uniformProb h03a hn a
      have hnotprob : uniformProb (fun e : Pair V => ¬ Touches a e.val) = 1-p := by
        rw [uniformProb_not, hprob]
      have hg0 : uniformMeanENN g0 = ENNReal.ofReal (1-p) := by
        calc
          uniformMeanENN g0 =
              ENNReal.ofReal (uniformProb (fun e : Pair V => ¬ Touches a e.val)) := by
                exact uniformMeanENN_indicator (α := Pair V)
                  (P := fun e : Pair V => ¬ Touches a e.val)
          _ = ENNReal.ofReal (1-p) := congrArg ENNReal.ofReal hnotprob
      have hg1 : uniformMeanENN g1 = ENNReal.ofReal p := by
        calc
          uniformMeanENN g1 =
              ENNReal.ofReal (uniformProb (fun e : Pair V => Touches a e.val)) := by
                unfold g1
                exact uniformMeanENN_indicator (α := Pair V)
                  (P := fun e : Pair V => Touches a e.val)
          _ = ENNReal.ofReal p := by
                simpa [p] using congrArg ENNReal.ofReal hprob
      have hf0 : uniformMeanENN f0 =
          ENNReal.ofReal (binomialWeight m p k) := by
        change uniformMeanENN (fun x : EdgeTuple V m =>
          if touchCount a x = k then (1 : ℝ≥0∞) else 0) = _
        exact ih k
      have hf1 : uniformMeanENN f1 = ENNReal.ofReal
          (if k = 0 then 0 else binomialWeight m p (k-1)) := by
        by_cases hk : k = 0
        · have hfzero : f1 = fun _ => (0 : ℝ≥0∞) := by
            funext x
            simp [f1, hk]
          rw [hfzero]
          simp [uniformMeanENN, hk]
        · have hpred (x : Fin m → Pair V) :
              (touchCount a x + 1 = k) ↔ touchCount a x = k-1 := by omega
          have hrewrite : f1 = fun x =>
              if touchCount a x = k-1 then (1 : ℝ≥0∞) else 0 := by
            funext x
            simp [f1, hpred x]
          rw [hrewrite]
          simpa [hk] using ih (k-1)
      have hprod0 := uniformMeanENN_snoc_prod h02 m f0 g0
      have hprod1 := uniformMeanENN_snoc_prod h02 m f1 g1
      rw [hprod0, hprod1, hf0, hg0, hf1, hg1]
      have hB (j : ℕ) : 0 ≤ binomialWeight m p j :=
        binomialWeight_nonneg m j p hp hq
      have hB0 := hB k
      have hBprev : 0 ≤ if k = 0 then 0 else binomialWeight m p (k-1) := by
        split_ifs
        · exact le_rfl
        · exact hB (k-1)
      have hterm0 :
          ENNReal.ofReal (binomialWeight m p k) * ENNReal.ofReal (1-p) =
            ENNReal.ofReal (binomialWeight m p k * (1-p)) := by
        rw [ENNReal.ofReal_mul hB0]
      have hterm1 :
          ENNReal.ofReal (if k = 0 then 0 else binomialWeight m p (k-1)) *
              ENNReal.ofReal p =
            ENNReal.ofReal ((if k = 0 then 0 else binomialWeight m p (k-1)) * p) := by
        rw [ENNReal.ofReal_mul hBprev]
      rw [hterm0, hterm1]
      rw [← ENNReal.ofReal_add (mul_nonneg hB0 hq) (mul_nonneg hBprev hp)]
      congr 1
      simpa [p] using (binomialWeight_succ m k p).symm

theorem S3_03bStatement_of_deps
    (h02 : ThLean.BP.S3.S3_02Statement.{u})
    (h03a : ThLean.BP.S3.S3_03aStatement.{u}) :
    ThLean.BP.S3.S3_03bStatement.{u,v} := by
  intro V W instV instW hn
  letI : Fintype V := instV
  letI : Fintype W := instW
  refine ⟨?_, ?_, ?_⟩
  · intro m k a
    have hpairPos : 0 < Fintype.card (Pair V) := (h03a V hn).2.1
    letI : Nonempty (Pair V) := Fintype.card_pos_iff.mp hpairPos
    letI : Nonempty (EdgeTuple V m) := ⟨fun _ => Classical.choice inferInstance⟩
    have hdist := touchCount_distributionENN h02 h03a hn a m k
    have hENN : uniformMeanENN (fun x : EdgeTuple V m =>
        if degree (tupleGraph x) a = k then (1 : ℝ≥0∞) else 0) =
        ENNReal.ofReal (binomialWeight m (2 / Fintype.card V) k) := by
      convert hdist using 1
      congr 1
      funext x
      rw [degree_tupleGraph_eq_touchCount]
    have hreal :
        graphProb m (fun G => degree G a = k) =
          binomialWeight m (2 / Fintype.card V) k := by
      have hprob_nonneg : 0 ≤ graphProb m (fun G => degree G a = k) := by
        change 0 ≤ uniformProb (fun x : EdgeTuple V m => degree (tupleGraph x) a = k)
        rw [uniformProb_eq_card_div]
        positivity
      have hweight_nonneg : 0 ≤ binomialWeight m (2 / Fintype.card V) k :=
        binomialWeight_nonneg m k _ (by positivity) (by
          have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
          have hcardR : (0 : ℝ) < Fintype.card V := by positivity
          rw [sub_nonneg, div_le_iff₀ hcardR]
          simpa using hnR)
      apply (ENNReal.ofReal_eq_ofReal_iff hprob_nonneg hweight_nonneg).mp
      have hENNreal := hENN
      have hindicator_fun :
          (fun x : EdgeTuple V m =>
            if degree (tupleGraph x) a = k then (1 : ℝ≥0∞) else 0) =
          (fun x : EdgeTuple V m =>
            @ite ℝ≥0∞ (degree (tupleGraph x) a = k)
              (Classical.propDecidable (degree (tupleGraph x) a = k)) 1 0) := by
        funext x
        by_cases hx : degree (tupleGraph x) a = k <;> simp [hx]
      rw [hindicator_fun] at hENNreal
      rw [uniformMeanENN_indicator
        (P := fun x : EdgeTuple V m => degree (tupleGraph x) a = k)] at hENNreal
      change ENNReal.ofReal (graphProb m (fun G => degree G a = k)) = _ at hENNreal
      exact hENNreal
    exact hreal
  · intro a
    exact touches_uniformProb h03a hn a
  · exact graphMeanENN_relabel

end ThLean.W.S303

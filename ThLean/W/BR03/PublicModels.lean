import ThLean.Defs.Bridge

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.BR03

open ThresholdFoundations

private def pairEquiv (n : ℕ) : ThresholdChallenge.Pair n ≃ Pair (Fin n) where
  toFun p := ⟨p.val, by
    simpa [ThresholdChallenge.completeEdges] using p.property⟩
  invFun p := ⟨p.val, by
    simpa [ThresholdChallenge.completeEdges] using p.property⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl

private def prefixEquiv (n m : ℕ) : ThresholdChallenge.EdgePrefix n m ≃ EdgeTuple (Fin n) m where
  toFun x i := pairEquiv n (x i)
  invFun x i := (pairEquiv n).symm (x i)
  left_inv := by intro x; funext i; exact (pairEquiv n).left_inv (x i)
  right_inv := by intro x; funext i; exact (pairEquiv n).right_inv (x i)

private lemma tupleGraph_pos_iff {n m : ℕ} (x : EdgeTuple (Fin n) m)
    (e : Sym2 (Fin n)) :
    0 < tupleGraph x e ↔ ∃ i, (x i).val = e := by
  letI : DecidablePred (fun i : Fin m => (x i).val = e) :=
    fun i => @Sym2.instDecidableEq (Fin n) (instDecidableEqFin n) (x i).val e
  simp only [tupleGraph, Finset.card_pos, Finset.filter_nonempty_iff,
    Finset.mem_univ, true_and]

private lemma prefixMultigraph_mem_iff {n m : ℕ} (x : ThresholdChallenge.EdgePrefix n m)
    (e : ThresholdChallenge.Pair n) :
    e ∈ ThresholdChallenge.prefixMultigraph x ↔ ∃ i, x i = e := by
  simp [ThresholdChallenge.prefixMultigraph]

private lemma prefixColorable_iff (q n m : ℕ) (x : ThresholdChallenge.EdgePrefix n m) :
    ThresholdChallenge.MultigraphColorable q (ThresholdChallenge.prefixMultigraph x) ↔
      Colorable q (tupleGraph ((prefixEquiv n m) x)) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro u v huv
    rw [tupleGraph_pos_iff] at huv
    obtain ⟨i, hi⟩ := huv
    apply hσ (x i)
    · exact (prefixMultigraph_mem_iff x (x i)).2 ⟨i, rfl⟩
    · simpa [prefixEquiv, pairEquiv] using hi
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro e he u v hev
    obtain ⟨i, rfl⟩ := (prefixMultigraph_mem_iff x e).1 he
    have hp : 0 < tupleGraph ((prefixEquiv n m) x) (s(u, v)) := by
      rw [tupleGraph_pos_iff]
      exact ⟨i, by simpa [prefixEquiv, pairEquiv] using hev⟩
    exact hσ u v hp

private lemma challenge_completeEdges_eq (n : ℕ) :
    ThresholdChallenge.completeEdges n = completeEdges (V := Fin n) := by
  ext e
  simp [ThresholdChallenge.completeEdges, completeEdges]

private lemma publicSimpleColorable_iff (q n : ℕ) (E : Finset (Sym2 (Fin n))) :
    ThresholdChallenge.Colorable q n E ↔ Colorable q (simpleGraph E) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro u v huv
    have hmem : s(u, v) ∈ E := by
      by_contra hnot
      simp [simpleGraph, hnot] at huv
    exact hσ u v hmem
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro u v huv
    apply hσ u v
    simp [simpleGraph, huv]

private lemma challenge_graphsWithEdges_eq (n m : ℕ) :
    ThresholdChallenge.graphsWithEdges n m = simpleGraphsWithEdges (V := Fin n) m := by
  simp [ThresholdChallenge.graphsWithEdges, simpleGraphsWithEdges,
    challenge_completeEdges_eq]

private lemma challenge_colorableGraphs_eq (q n m : ℕ) :
    (ThresholdChallenge.graphsWithEdges n m).filter (ThresholdChallenge.Colorable q n) =
      (simpleGraphsWithEdges (V := Fin n) m).filter
        (fun E => Colorable q (simpleGraph E)) := by
  rw [challenge_graphsWithEdges_eq]
  ext E
  simp [publicSimpleColorable_iff]

private lemma processSurvival_eq (q n m : ℕ) :
    ThresholdChallenge.processSurvival q n m = processSurvival (V := Fin n) q m := by
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  letI : Fintype (Pair (Fin n)) :=
    @Subtype.fintype (Sym2 (Fin n)) (fun e => ∀ v : Fin n, e ≠ s(v, v))
      (fun e => Fintype.decidableForallFintype) (inferInstance : Fintype (Sym2 (Fin n)))
  letI : Fintype (EdgeTuple (Fin n) m) :=
    @Pi.instFintype (Fin m) (fun _ => Pair (Fin n)) (instDecidableEqFin m)
      (Fin.fintype m) (fun _ => inferInstance)
  have hcard : Fintype.card (ThresholdChallenge.EdgePrefix n m) =
      Fintype.card (EdgeTuple (Fin n) m) := Fintype.card_congr (prefixEquiv n m)
  have hsum :
      (∑ x : ThresholdChallenge.EdgePrefix n m,
        indicator (ThresholdChallenge.MultigraphColorable q (ThresholdChallenge.prefixMultigraph x))) =
      ∑ y : EdgeTuple (Fin n) m, indicator
        (Colorable q (tupleGraph y)) := by
    apply Fintype.sum_equiv (prefixEquiv n m)
    intro x
    have hi := prefixColorable_iff q n m x
    by_cases h : ThresholdChallenge.MultigraphColorable q (ThresholdChallenge.prefixMultigraph x)
    · have h' := hi.mp h
      simp [indicator, h, h']
    · have h' : ¬ Colorable q (tupleGraph ((prefixEquiv n m) x)) := fun hc => h (hi.mpr hc)
      simp [indicator, h, h']
  have hnum :
      (((Finset.univ.filter (fun x : ThresholdChallenge.EdgePrefix n m =>
        ThresholdChallenge.MultigraphColorable q (ThresholdChallenge.prefixMultigraph x))).card : ℕ) : ℝ) =
      ∑ x : ThresholdChallenge.EdgePrefix n m,
        indicator (ThresholdChallenge.MultigraphColorable q (ThresholdChallenge.prefixMultigraph x)) := by
    rw [Finset.card_filter]
    simp [indicator]
  have hden : (Fintype.card (ThresholdChallenge.EdgePrefix n m) : ℝ) =
      (Fintype.card (EdgeTuple (Fin n) m) : ℝ) := by exact_mod_cast hcard
  unfold ThresholdChallenge.processSurvival processSurvival survival uniformProb uniformMean
  simp only [zero_add]
  rw [hnum, hden]
  exact congrArg (fun z : ℝ => z / (Fintype.card (EdgeTuple (Fin n) m) : ℝ)) hsum

private lemma completeEdges_card (n : ℕ) :
    (completeEdges (V := Fin n)).card = n.choose 2 := by
  have h : completeEdges (V := Fin n) = (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    ext e
    refine Sym2.ind ?_ e
    intro a b
    simp [ThresholdFoundations.completeEdges, SimpleGraph.edgeFinset,
      Sym2.mk_isDiag_iff, eq_comm]
  rw [h]
  simpa using (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))

private lemma bernoulliWeights_total {n : ℕ} (S : Finset (Sym2 (Fin n))) (p : ℝ) :
    (∑ E ∈ S.powerset, p ^ E.card * (1 - p) ^ (S.card - E.card)) = 1 := by
  classical
  calc
    (∑ E ∈ S.powerset, p ^ E.card * (1 - p) ^ (S.card - E.card)) =
        ∑ E ∈ S.powerset,
          (∏ e ∈ E, p) * ∏ e ∈ S \ E, (1 - p) := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.prod_const, Finset.prod_const,
        Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hE)]
    _ = ∏ e ∈ S, (p + (1 - p)) := (Finset.prod_add _ _ _).symm
    _ = 1 := by simp

private lemma bernoulliProbability_bounds (q n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ bernoulliProbability (V := Fin n) q p ∧
      bernoulliProbability (V := Fin n) q p ≤ 1 := by
  let S := completeEdges (V := Fin n)
  have hcard : S.card = n.choose 2 := by
    simpa [S] using completeEdges_card n
  have htotal :
      (∑ E ∈ S.powerset, p ^ E.card * (1 - p) ^ (n.choose 2 - E.card)) = 1 := by
    simpa [hcard] using bernoulliWeights_total S p
  have hweight (E : Finset (Sym2 (Fin n))) :
      0 ≤ p ^ E.card * (1 - p) ^ (n.choose 2 - E.card) := by
    positivity
  constructor
  · unfold bernoulliProbability
    apply Finset.sum_nonneg
    intro E hE
    by_cases hc : Colorable q (simpleGraph E)
    · simp [indicator, hc]
      positivity
    · simp [indicator, hc]
  · unfold bernoulliProbability
    simp only [Fintype.card_fin]
    change (∑ E ∈ S.powerset,
        p ^ E.card * (1 - p) ^ (n.choose 2 - E.card) *
          indicator (Colorable q (simpleGraph E))) ≤ 1
    calc
      (∑ E ∈ S.powerset,
          p ^ E.card * (1 - p) ^ (n.choose 2 - E.card) *
            indicator (Colorable q (simpleGraph E))) ≤
        ∑ E ∈ S.powerset, p ^ E.card * (1 - p) ^ (n.choose 2 - E.card) := by
          apply Finset.sum_le_sum
          intro E hE
          by_cases hc : Colorable q (simpleGraph E)
          · simp [indicator, hc]
          · simp [indicator, hc]
            exact hweight E
      _ = 1 := htotal

theorem PublicModelsStatement_holds : ThresholdFoundations.PublicModelsStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun q n m => processSurvival_eq q n m
  · intro q n m
    unfold ThresholdChallenge.uniformColorabilityProbability simpleProbability
    rw [challenge_colorableGraphs_eq, challenge_graphsWithEdges_eq]
  · intro q n p
    simp [ThresholdChallenge.binomialColorabilityProbability, bernoulliProbability,
      challenge_completeEdges_eq, publicSimpleColorable_iff, indicator, Fintype.card_fin]
  · intro q n d
    simp [ThresholdChallenge.sparseBinomialProbability, sparseProbability,
      ThresholdChallenge.binomialColorabilityProbability, bernoulliProbability,
      challenge_completeEdges_eq, publicSimpleColorable_iff, indicator, Fintype.card_fin]
  · intro q
    rfl
  · intro q n d hn hd0 hdn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hp0 : 0 ≤ d / (n : ℝ) := div_nonneg hd0 (le_of_lt hnR)
    have hp1 : d / (n : ℝ) ≤ 1 :=
      (div_le_iff₀ hnR).2 (by simpa using hdn)
    have hsparse : sparseProbability q n d =
        bernoulliProbability (V := Fin n) q (d / (n : ℝ)) := by
      simp [sparseProbability, hn, hd0, hdn]
    rw [hsparse]
    exact bernoulliProbability_bounds q n (d / (n : ℝ)) hp0 hp1

example : ThresholdFoundations.PublicModelsStatement :=
  ThLean.W.BR03.PublicModelsStatement_holds


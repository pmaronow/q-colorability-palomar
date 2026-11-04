module

public import ThLean.Contrib.S553.Nodes

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S553
open ThresholdFoundations

private lemma uniformMean_nonneg {A : Type} [Fintype A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  unfold uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg fun a _ => hf a
  · exact Nat.cast_nonneg _

private lemma uniformProb_nonneg {A : Type} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProb P := by
  apply uniformMean_nonneg
  intro a
  simp only [indicator]
  split_ifs <;> norm_num

private def appendLast {V : Type*} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (e : Pair V) : EdgeTuple V (m + 1) :=
  Fin.snoc x e

private theorem tupleGraph_appendLast {V : Type*} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (e : Pair V) :
    tupleGraph (appendLast x e) = addPair (tupleGraph x) e := by
  classical
  funext z
  simp only [tupleGraph, addPair, addEdge, Function.update, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [appendLast, Fin.snoc_castSucc, Fin.snoc_last]
  by_cases hz : z = e.val
  · subst z
    simp
  · simp [hz]
    intro hz'
    exact hz hz'.symm

private def splitLastEquiv {V : Type*} [Fintype V] (m : ℕ) :
    EdgeTuple V (m + 1) ≃ (EdgeTuple V m × Pair V) where
  toFun x := (Fin.init x, x (Fin.last m))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := by simp
  right_inv p := by
    rcases p with ⟨x, e⟩
    simp

private lemma uniformMean_sub {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_sub_distrib]
  ring

private lemma uniformMean_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

private lemma uniformMean_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  unfold uniformMean
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    have hp : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ‹Nonempty A›
    exact_mod_cast ne_of_gt hp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

private lemma uniformMean_fubini {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a, b))) := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    have hp : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ‹Nonempty A›
    exact_mod_cast ne_of_gt hp
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    have hp : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ‹Nonempty B›
    exact_mod_cast ne_of_gt hp
  unfold uniformMean
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  simp_rw [Finset.sum_div]
  simp only [Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private lemma uniformMean_init {V : Type} [Fintype V] [Nonempty (Pair V)]
    {m : ℕ} (f : EdgeTuple V m → ℝ) :
    uniformMean (fun x : EdgeTuple V (m + 1) => f (Fin.init x)) = uniformMean f := by
  let e := splitLastEquiv (V := V) m
  calc
    uniformMean (fun x : EdgeTuple V (m + 1) => f (Fin.init x)) =
        uniformMean (fun p : EdgeTuple V m × Pair V => f p.1) := by
      have hf := uniformMean_equiv e (fun p : EdgeTuple V m × Pair V => f p.1)
      simpa [e, splitLastEquiv] using hf
    _ = uniformMean (fun x : EdgeTuple V m => uniformMean (fun _ : Pair V => f x)) := by
      exact (uniformMean_fubini (A := EdgeTuple V m) (B := Pair V)
        (fun p : EdgeTuple V m × Pair V => f p.1))
    _ = uniformMean f := by
      congr 1
      funext x
      exact uniformMean_const (A := Pair V) (f x)

private lemma pair_nonempty_of_card {V : Type} [Fintype V]
    (hn : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  classical
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hv
  rw [Sym2.eq_iff] at hv
  rcases hv with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hab (ha.trans hb.symm)
  · exact hab (ha.trans hb.symm)

private lemma addPair_subgraph {V : Type} [Fintype V]
    (G : MGraph V) (e : Pair V) : subgraph G (addPair G e) := by
  intro z
  by_cases hz : z = e.val
  · subst z
    simp [addPair, addEdge]
  · simp [addPair, addEdge, hz]

private lemma colorable_of_subgraph {V : Type} [Fintype V]
    (q : ℕ) {G G' : MGraph V} (hs : subgraph G G') :
    Colorable q G' → Colorable q G := by
  rintro ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro u v huv
  exact hσ u v (lt_of_lt_of_le huv (hs (s(u, v))))

private theorem colorable_addPair_iff {V : Type} [Fintype V]
    (q : ℕ) (G : MGraph V) (e : Pair V) :
    Colorable q (addPair G e) ↔ Colorable q G ∧ ¬ FrozenPair q G e := by
  constructor
  · intro hAdd
    refine ⟨colorable_of_subgraph q (addPair_subgraph G e) hAdd, ?_⟩
    intro hFrozenPair
    obtain ⟨u, v, heq, hFrozen⟩ := hFrozenPair
    rcases hAdd with ⟨σ, hσ⟩
    rcases hFrozen with ⟨hG, hConst⟩
    have hGσ : IsColoring q G σ := by
      intro a b hab
      exact hσ a b (lt_of_lt_of_le hab (addPair_subgraph G e (s(a, b))))
    have hEdge : 0 < addPair G e (s(u, v)) := by
      simp [addPair, addEdge, heq]
    have hDiff := hσ u v hEdge
    exact hDiff (hConst σ hGσ)
  · rintro ⟨⟨σ, hσ⟩, hNotFrozen⟩
    have hrepr : e.val = s(e.val.out.1, e.val.out.2) := by
      exact (Quot.out_eq e.val).symm
    let a := e.val.out.1
    let b := e.val.out.2
    have hab : a ≠ b := by
      intro h
      exact e.property a (hrepr.trans (congrArg (fun y => s(a, y)) h.symm))
    have hnot : ¬ Frozen q G a b := by
      intro hf
      exact hNotFrozen ⟨a, b, hrepr, hf⟩
    have hex : ∃ τ, IsColoring q G τ ∧ τ a ≠ τ b := by
      by_contra h
      apply hnot
      refine ⟨⟨σ, hσ⟩, ?_⟩
      intro τ hτ
      by_contra hneq
      exact h ⟨τ, hτ, hneq⟩
    obtain ⟨τ, hτ, hτab⟩ := hex
    refine ⟨τ, ?_⟩
    intro u v huv
    by_cases hG : 0 < G (s(u, v))
    · exact hτ u v hG
    · by_cases he : e.val = s(u, v)
      · have hnew : 0 < addPair G e (s(u, v)) := by
          simp [addPair, addEdge, he]
        have he' : s(a, b) = s(u, v) := hrepr.symm.trans he
        rcases Sym2.eq_iff.mp he' with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
        · subst u
          subst v
          exact hτab
        · subst u
          subst v
          exact hτab.symm
      · have heRev : s(u, v) ≠ e.val := fun h => he h.symm
        have hold : 0 < G (s(u, v)) := by
          simpa [addPair, addEdge, Function.update, heRev] using huv
        exact (hG hold).elim

/-- The pointwise finite-step hazard identity. -/
theorem S5_11HazardIncrementStatement_holds :
    ThLean.Contrib.S553.S5_11HazardIncrementStatement := by
  intro V instV q hq hn m
  haveI : Nonempty (Pair V) := pair_nonempty_of_card hn
  let event (x : EdgeTuple V m) (e : Pair V) : Prop :=
    Colorable q (tupleGraph x) ∧
      ¬ Colorable q (addPair (tupleGraph x) e)
  have hevent (x : EdgeTuple V m) (e : Pair V) :
      event x e ↔ FrozenPair q (tupleGraph x) e := by
    constructor
    · rintro ⟨hc, hbad⟩
      by_contra hnot
      exact hbad ((colorable_addPair_iff q (tupleGraph x) e).2 ⟨hc, hnot⟩)
    · intro hfp
      obtain ⟨u, v, huv, hfr⟩ := hfp
      have hc : Colorable q (tupleGraph x) := hfr.1
      refine ⟨hc, ?_⟩
      intro hadd
      exact ((colorable_addPair_iff q (tupleGraph x) e).1 hadd).2 ⟨u, v, huv, hfr⟩
  have hpoint (x : EdgeTuple V m) :
      kappa q (tupleGraph x) = uniformMean (fun e : Pair V => indicator (event x e)) := by
    change uniformMean (fun e : Pair V => indicator (FrozenPair q (tupleGraph x) e)) = _
    congr 1
    funext e
    exact congrArg indicator (propext (hevent x e).symm)
  let ev : EdgeTuple V m × Pair V → ℝ := fun p => indicator (event p.1 p.2)
  have hfubini := uniformMean_fubini ev
  let eappend := splitLastEquiv (V := V) m
  have hreindex := uniformMean_equiv eappend ev
  have hgraph (x : EdgeTuple V (m + 1)) :
      tupleGraph x = addPair (tupleGraph (Fin.init x)) (x (Fin.last m)) := by
    calc
      tupleGraph x = tupleGraph (Fin.snoc (Fin.init x) (x (Fin.last m))) := by
        rw [Fin.snoc_init_self]
      _ = addPair (tupleGraph (Fin.init x)) (x (Fin.last m)) :=
        tupleGraph_appendLast (Fin.init x) (x (Fin.last m))
  have hiff (x : EdgeTuple V (m + 1)) :
      Colorable q (tupleGraph x) ↔
        Colorable q (tupleGraph (Fin.init x)) ∧
          ¬ FrozenPair q (tupleGraph (Fin.init x)) (x (Fin.last m)) := by
    rw [hgraph x]
    exact colorable_addPair_iff q (tupleGraph (Fin.init x)) (x (Fin.last m))
  have hdiff (x : EdgeTuple V (m + 1)) :
      indicator (Colorable q (tupleGraph (Fin.init x)) ∧
        ¬ Colorable q (tupleGraph x)) =
      indicator (Colorable q (tupleGraph (Fin.init x))) -
        indicator (Colorable q (tupleGraph x)) := by
    by_cases hp : Colorable q (tupleGraph (Fin.init x))
    · by_cases ht : Colorable q (tupleGraph x) <;>
        simp [indicator, hp, ht]
    · have ht : ¬ Colorable q (tupleGraph x) := by
        intro hc
        exact hp (hiff x |>.mp hc).1
      simp [indicator, hp, ht]
  have hprefixLaw :
      uniformMean (fun x : EdgeTuple V (m + 1) =>
        indicator (Colorable q (tupleGraph (Fin.init x)))) =
      uniformMean (fun x : EdgeTuple V m =>
        indicator (Colorable q (tupleGraph x))) := by
    exact uniformMean_init (fun x : EdgeTuple V m =>
      indicator (Colorable q (tupleGraph x)))
  have hsurv (r : ℕ) :
      survival q (0 : MGraph V) r =
        uniformMean (fun x : EdgeTuple V r =>
          indicator (Colorable q (tupleGraph x))) := by
    simp [survival, uniformProb]
  calc
    uniformMean (fun x : EdgeTuple V m => kappa q (tupleGraph x)) =
        uniformMean (fun x : EdgeTuple V m =>
          uniformMean (fun e : Pair V => indicator (event x e))) := by
      congr 1
      funext x
      exact hpoint x
    _ = uniformMean ev := hfubini.symm
    _ = uniformMean (fun x : EdgeTuple V (m + 1) => ev (eappend x)) := hreindex.symm
    _ = uniformMean (fun x : EdgeTuple V (m + 1) =>
          indicator (Colorable q (tupleGraph (Fin.init x)) ∧
            ¬ Colorable q (tupleGraph x))) := by
      congr 1
      funext x
      change indicator (event (Fin.init x) (x (Fin.last m))) = _
      simp only [event]
      rw [hgraph x]
    _ = uniformMean (fun x : EdgeTuple V (m + 1) =>
          indicator (Colorable q (tupleGraph (Fin.init x))) -
            indicator (Colorable q (tupleGraph x))) := by
      congr 1
      funext x
      exact hdiff x
    _ = processSurvival (V := V) q m - processSurvival (V := V) q (m + 1) := by
      rw [uniformMean_sub, hprefixLaw, ← hsurv m, ← hsurv (m + 1)]
      rfl
    _ = hittingMass (V := V) q m := rfl

/-- The finite-step identity and the nonnegative occupation formula imply the
low-added hazard budget, including when the process has positive survival at
infinite time. -/
theorem S5_11Statement_of_helpers
    (hinc : ThLean.Contrib.S553.S5_11HazardIncrementStatement)
    (h10 : ThLean.BP.S5.S5_10Statement) :
    ThLean.BP.S5.S5_11Statement := by
  intro V instV q hq hn
  let a : ℕ → ℝ := fun m =>
    uniformMean (fun x : EdgeTuple V m => kappa q (tupleGraph x))
  have ha_nonneg : ∀ m, 0 ≤ a m := by
    intro m
    apply uniformMean_nonneg
    intro x
    exact uniformProb_nonneg (FrozenPair q (tupleGraph x))
  have ha_step : ∀ m, a m = hittingMass (V := V) q m := by
    intro m
    exact hinc V q hq hn m
  have hs0 : processSurvival (V := V) q 0 = 1 := by
    have hg (x : EdgeTuple V 0) : tupleGraph x = 0 := by
      ext e
      simp [tupleGraph]
    have hc (x : EdgeTuple V 0) : Colorable q (tupleGraph x) := by
      rw [hg]
      refine ⟨fun _ => (⟨0, by omega⟩ : Fin q), ?_⟩
      intro u v he
      simp at he
    simp [processSurvival, survival, uniformProb, uniformMean, indicator, hc]
  have hsurv_nonneg : ∀ m, 0 ≤ processSurvival (V := V) q m := by
    intro m
    simp only [processSurvival, survival]
    exact uniformProb_nonneg _
  have hsurv_step : ∀ m,
      processSurvival (V := V) q (m + 1) ≤ processSurvival (V := V) q m := by
    intro m
    have := ha_nonneg m
    rw [ha_step m, hittingMass] at this
    linarith
  have hanti : Antitone (processSurvival (V := V) q) :=
    antitone_nat_of_succ_le hsurv_step
  have hbdd : BddBelow (Set.range (processSurvival (V := V) q)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨m, rfl⟩
    exact hsurv_nonneg m
  have hlim : Tendsto (processSurvival (V := V) q) atTop
      (𝓝 (infiniteHittingProbability (V := V) q)) := by
    rw [infiniteHittingProbability, sInf_range]
    exact tendsto_atTop_ciInf hanti hbdd
  have htel : ∀ n,
      (∑ m ∈ Finset.range n, a m) =
        1 - processSurvival (V := V) q n := by
    intro n
    induction n with
    | zero => simp [hs0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, ha_step n, hittingMass]
      ring
  have hpartial : Tendsto (fun n => ∑ m ∈ Finset.range n, a m) atTop
      (𝓝 (1 - infiniteHittingProbability (V := V) q)) := by
    have hEq : (fun n : ℕ => ∑ m ∈ Finset.range n, a m) =
        (fun n => (1 : ℝ) - processSurvival (V := V) q n) := funext htel
    rw [hEq]
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    exact hconst.sub hlim
  have hhas : HasSum a (1 - infiniteHittingProbability (V := V) q) :=
    (hasSum_iff_tendsto_nat_of_nonneg ha_nonneg _).2 hpartial
  have hinf_nonneg : 0 ≤ infiniteHittingProbability (V := V) q := by
    rw [infiniteHittingProbability]
    apply le_csInf ⟨processSurvival (V := V) q 0, Set.mem_range_self 0⟩
    intro y hy
    rcases hy with ⟨m, rfl⟩
    exact hsurv_nonneg m
  have hsum_le : ∑' m, a m ≤ 1 := by
    rw [hhas.tsum_eq]
    linarith
  refine ⟨hhas, ?_⟩
  intro p hp
  rcases h10 p hp with ⟨_, h10R⟩
  have hdata := h10R a ha_nonneg hhas.summable
  rcases hdata with ⟨hint, heq⟩
  refine ⟨?_, ?_⟩
  · simpa [poissonGraphMean, a] using hint
  · rw [show (fun t => poissonGraphMean (p * t) (kappa q)) =
        (fun t => poissonMixture (p * t) a) by rfl, heq]
    have hfac : 0 ≤ 1 / p := by positivity
    calc
      (1 / p) * ∑' m, a m ≤ (1 / p) * 1 := mul_le_mul_of_nonneg_left hsum_le hfac
      _ = 1 / p := by ring

/-- Apply the occupation theorem from the sole sibling dependency S5_10. -/
theorem S5_11Statement_of_deps
    (h10 : ThLean.BP.S5.S5_10Statement) :
    ThLean.BP.S5.S5_11Statement := by
  exact S5_11Statement_of_helpers S5_11HazardIncrementStatement_holds h10

end ThLean.W.S553

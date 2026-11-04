module

public import ThLean.BP.S4.Bridges

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S432
open ThresholdFoundations
open ThLean.BP.S4
set_option maxHeartbeats 1000000

private theorem uniformMean_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

private theorem uniformMean_fintype_irrel {A : Type} (i j : Fintype A) (f : A → ℝ) :
    @uniformMean A i f = @uniformMean A j f := by
  have h : i = j := Subsingleton.elim i j
  cases h
  rfl

private theorem uniformMean_congr {A : Type} [Fintype A] (f g : A → ℝ)
    (h : ∀ a, f a = g a) : uniformMean f = uniformMean g := by
  congr 1
  funext a
  exact h a

private theorem uniformMean_prod {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := A))
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := B))
  rw [Finset.sum_div]
  conv_rhs => rw [← Finset.sum_div]
  conv_lhs => rw [← Finset.sum_div]
  field_simp [hA, hB]
  rw [Nat.cast_mul]
  ring

private theorem uniformMean_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  unfold uniformMean
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := A))
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.card_univ]
  field_simp [hA]

private theorem indicator_sub {P Q : Prop} (h : Q → P) :
    indicator P - indicator Q = indicator (P ∧ ¬ Q) := by
  by_cases hp : P
  · by_cases hq : Q <;> simp [indicator, hp, hq]
  · have hq : ¬ Q := fun hq => hp (h hq)
    simp [indicator, hp, hq]

private theorem uniformMean_prod_snd {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : B → ℝ) :
    uniformMean (fun p : A × B => f p.2) = uniformMean f := by
  rw [uniformMean_prod]
  simp only [Prod.snd]
  exact uniformMean_const _

private theorem uniformMean_prod_fst {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A → ℝ) :
    uniformMean (fun p : A × B => f p.1) = uniformMean f := by
  rw [uniformMean_prod]
  simp only [Prod.fst]
  simp_rw [uniformMean_const]

private theorem uniformMean_prefix_succ {E : Type} [Fintype E] [Nonempty E]
    (m : ℕ) (f : (Fin m → E) → ℝ) :
    uniformMean (fun x : Fin (m+1) → E => f (fun i => x i.castSucc)) = uniformMean f := by
  let e : E × (Fin m → E) ≃ (Fin (m+1) → E) := Fin.snocEquiv (fun _ : Fin (m+1) => E)
  calc
    uniformMean (fun x : Fin (m+1) → E => f (fun i => x i.castSucc)) =
        uniformMean (fun p : E × (Fin m → E) => f (fun i => (e p) i.castSucc)) :=
      (uniformMean_equiv e _).symm
    _ = uniformMean (fun p : E × (Fin m → E) => f p.2) := by
      congr 1
      funext p
      congr 1
      funext i
      simp [e, Fin.snocEquiv]
    _ = uniformMean f := uniformMean_prod_snd f

private theorem tupleGraph_snoc {V : Type} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (e : Pair V) :
    tupleGraph (Fin.snoc x e) = addPair (tupleGraph x) e := by
  ext d
  simp only [tupleGraph, addPair, addEdge]
  rw [Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp only [tupleGraph, Finset.card_filter]
  by_cases hd : d = e.val
  · subst d
    rw [Function.update_self]
    simp only [if_true]
  · have hne : e.val ≠ d := Ne.symm hd
    rw [Function.update_of_ne hd]
    simp only [if_neg hne, tupleGraph, Finset.card_filter, add_zero]

private theorem subgraph_addPair {V : Type} (G : MGraph V) (e : Pair V) :
    subgraph G (addPair G e) := by
  intro d
  by_cases hd : d = e.val
  · subst d
    simp [addPair, addEdge]
  · rw [addPair, addEdge, Function.update_of_ne hd]

private theorem colorable_of_subgraph {V : Type} [Fintype V] {q : ℕ}
    {G G' : MGraph V} (hsub : subgraph G G') : Colorable q G' → Colorable q G := by
  rintro ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro u v huv
  exact hσ u v (lt_of_lt_of_le huv (hsub (s(u,v))))

private theorem isColoring_addPair_iff {V : Type} [Fintype V] (q : ℕ)
    (G : MGraph V) (e : Pair V) (σ : V → Fin q) (u v : V)
    (he : e.val = s(u,v)) :
    IsColoring q (addPair G e) σ ↔ IsColoring q G σ ∧ σ u ≠ σ v := by
  constructor
  · intro hσ
    constructor
    · intro a b hab
      exact hσ a b (lt_of_lt_of_le hab (subgraph_addPair G e (s(a,b))))
    · have hpos : 0 < addPair G e (s(u,v)) := by
        simp [addPair, addEdge, he]
      exact hσ u v hpos
  · rintro ⟨hσ, hsep⟩ a b hab
    by_cases heq : e.val = s(a,b)
    · have hpair : s(a,b) = s(u,v) := heq.symm.trans he
      rcases Sym2.eq_iff.mp hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hsep
      · exact hsep.symm
    · have hne : s(a,b) ≠ e.val := Ne.symm heq
      have habG : 0 < G (s(a,b)) := by
        simpa [addPair, addEdge, Function.update_of_ne hne] using hab
      exact hσ a b habG

private theorem frozenPair_transition_iff {V : Type} [Fintype V] (q : ℕ)
    (G : MGraph V) (e : Pair V) :
    FrozenPair q G e ↔ Colorable q G ∧ ¬ Colorable q (addPair G e) := by
  constructor
  · rintro ⟨u,v,he,hfrozen⟩
    rcases hfrozen with ⟨hcolorable, hsame⟩
    refine ⟨hcolorable, ?_⟩
    rintro ⟨σ,hσ⟩
    have hparts := (isColoring_addPair_iff q G e σ u v he).mp hσ
    exact hparts.2 (hsame σ hparts.1)
  · rintro ⟨hcolorable, hfail⟩
    have hreps : ∃ u v, e.val = s(u,v) := by
      exact (Sym2.exists (f := fun z => e.val = z)).mp ⟨e.val, rfl⟩
    rcases hreps with ⟨u,v,he⟩
    have hsame : ∀ σ, IsColoring q G σ → σ u = σ v := by
      intro σ hσ
      by_contra hne
      apply hfail
      exact ⟨σ, (isColoring_addPair_iff q G e σ u v he).2 ⟨hσ, hne⟩⟩
    exact ⟨u,v,he,hcolorable,hsame⟩

private theorem terminalStep_one_eq_graphMean {V : Type} [Fintype V]
    (q m : ℕ) :
    terminalStep (V := V) q m (fun _ _ => 1) =
      graphMean (V := V) m (fun G => kappa q G) := by
  unfold terminalStep graphMean
  congr 1
  funext x
  simp only [kappa, uniformProb]
  congr 1
  funext e
  simp [indicator, frozenPair_transition_iff]

private theorem uniformMean_sub {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_sub_distrib]
  ring

private theorem pair_nonempty_of_two {n : ℕ} (hn : 2 ≤ n) :
    Nonempty (Pair (Fin n)) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [a,b] at hv
  refine ⟨⟨s(a,b), ?_⟩⟩
  intro v hv
  rcases Sym2.eq_iff.mp hv with ⟨hav,hbv⟩ | ⟨hav,hbv⟩
  · exact hab (hav.trans hbv.symm)
  · exact hab (hav.trans hbv.symm)

private theorem processSurvival_lift {n m : ℕ} (q : ℕ)
    [Nonempty (Pair (Fin n))] :
    processSurvival (V := Fin n) q m =
      uniformMean (fun p : EdgeTuple (Fin n) m × Pair (Fin n) =>
        indicator (Colorable q (tupleGraph p.1))) := by
  simp only [processSurvival, survival, uniformProb, zero_add]
  convert (uniformMean_prod_fst (A := EdgeTuple (Fin n) m) (B := Pair (Fin n))
    (f := fun x => indicator (Colorable q (tupleGraph x)))).symm using 1
  all_goals first | exact uniformMean_fintype_irrel _ _ _ | exact Subsingleton.elim _ _ | rfl

private theorem processSurvival_succ_prod {n m : ℕ} (q : ℕ)
    [Nonempty (Pair (Fin n))] :
    processSurvival (V := Fin n) q (m+1) =
      uniformMean (fun p : EdgeTuple (Fin n) m × Pair (Fin n) =>
        indicator (Colorable q (tupleGraph (Fin.snoc p.1 p.2)))) := by
  let e : (EdgeTuple (Fin n) m × Pair (Fin n)) ≃ EdgeTuple (Fin n) (m+1) :=
    (Equiv.prodComm (EdgeTuple (Fin n) m) (Pair (Fin n))).trans
      (Fin.snocEquiv (fun _ : Fin (m+1) => Pair (Fin n)))
  simp only [processSurvival, survival, uniformProb, zero_add]
  convert (uniformMean_equiv e
    (fun x : EdgeTuple (Fin n) (m+1) => indicator (Colorable q (tupleGraph x)))).symm using 1
  all_goals first | exact uniformMean_fintype_irrel _ _ _ | exact Subsingleton.elim _ _ | rfl

private theorem terminalStep_one_eq_prod {V : Type} [Fintype V]
    [Nonempty (Pair V)] (q m : ℕ) :
    terminalStep (V := V) q m (fun _ _ => 1) =
      uniformMean (fun p : EdgeTuple V m × Pair V =>
        indicator (Colorable q (tupleGraph p.1) ∧
          ¬ Colorable q (addPair (tupleGraph p.1) p.2))) := by
  simp only [terminalStep, Function.const_apply, indicator]
  convert (uniformMean_prod (fun p : EdgeTuple V m × Pair V =>
    if Colorable q (tupleGraph p.1) ∧
      ¬ Colorable q (addPair (tupleGraph p.1) p.2) then 1 else 0)).symm using 1
  all_goals first
    | exact uniformMean_fintype_irrel _ _ _
    | exact Subsingleton.elim _ _
    | (apply uniformMean_congr; intro p; by_cases hp :
        Colorable q (tupleGraph p.1) ∧ ¬ Colorable q (addPair (tupleGraph p.1) p.2) <;> simp [hp])
    | rfl

private theorem survival_step {n m : ℕ} (q : ℕ)
    [Nonempty (Pair (Fin n))] :
    processSurvival (V := Fin n) q m - processSurvival (V := Fin n) q (m+1) =
      terminalStep (V := Fin n) q m (fun _ _ => 1) := by
  rw [processSurvival_lift, processSurvival_succ_prod, terminalStep_one_eq_prod]
  rw [← uniformMean_sub]
  have hpoint : ∀ p : EdgeTuple (Fin n) m × Pair (Fin n),
      indicator (Colorable q (tupleGraph p.1)) -
        indicator (Colorable q (tupleGraph (Fin.snoc p.1 p.2))) =
      indicator (Colorable q (tupleGraph p.1) ∧
        ¬ Colorable q (addPair (tupleGraph p.1) p.2)) := by
    intro p
    have hsub : subgraph (tupleGraph p.1) (addPair (tupleGraph p.1) p.2) :=
      subgraph_addPair (tupleGraph p.1) p.2
    have hcolor : Colorable q (addPair (tupleGraph p.1) p.2) →
        Colorable q (tupleGraph p.1) := colorable_of_subgraph hsub
    rw [tupleGraph_snoc]
    exact indicator_sub hcolor
  convert (uniformMean_congr
    (fun p : EdgeTuple (Fin n) m × Pair (Fin n) =>
      indicator (Colorable q (tupleGraph p.1)) -
        indicator (Colorable q (tupleGraph (Fin.snoc p.1 p.2))))
    (fun p : EdgeTuple (Fin n) m × Pair (Fin n) =>
      indicator (Colorable q (tupleGraph p.1) ∧
        ¬ Colorable q (addPair (tupleGraph p.1) p.2))) hpoint) using 1
  all_goals first | exact uniformMean_fintype_irrel _ _ _ | exact Subsingleton.elim _ _

theorem S4_BRIDGE_01AStatement_of_deps
    (h08a : ThLean.BP.S4.S4_RED_08AStatement)
    (h08b : ThLean.BP.S4.S4_RED_08BStatement) :
    ThLean.BP.S4.S4_BRIDGE_01AStatement := by
  intro q n hq hn L U hLU
  letI : Nonempty (Pair (Fin n)) := pair_nonempty_of_two (by omega)
  constructor
  · have hterminal :
        terminalProb (V := Fin n) q L U (fun _ _ => True) =
          ∑ k ∈ Finset.Ico L U, terminalStep (V := Fin n) q k (fun _ _ => 1) := by
      have ha0 := h08a q n hq hn L U hLU (fun _ _ => 1)
      have ha : terminalReal (V := Fin n) q L U (fun _ _ _ => 1) =
          ∑ k ∈ Finset.Ico L U,
            graphMean (V := Fin n) k (fun G => kappa q G) := by
        convert ha0 using 1
        all_goals first
          | exact uniformMean_fintype_irrel _ _ _
          | exact Subsingleton.elim _ _
          | (apply Finset.sum_congr rfl; intro k hk; simp only [graphMean, mul_one];
              exact uniformMean_fintype_irrel _ _ _)
          | rfl
      calc
        terminalProb (V := Fin n) q L U (fun _ _ => True) =
            terminalReal (V := Fin n) q L U (fun _ _ _ => 1) := by
          simp [terminalProb, indicator]
        _ = ∑ k ∈ Finset.Ico L U,
              graphMean (V := Fin n) k (fun G => kappa q G) := ha
        _ = ∑ k ∈ Finset.Ico L U,
              terminalStep (V := Fin n) q k (fun _ _ => 1) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact (terminalStep_one_eq_graphMean (V := Fin n) q k).symm
    have hRange (N : ℕ) :
        (∑ k ∈ Finset.range N,
          (processSurvival (V := Fin n) q k - processSurvival (V := Fin n) q (k+1))) =
          processSurvival (V := Fin n) q 0 - processSurvival (V := Fin n) q N := by
      calc
        (∑ k ∈ Finset.range N,
          (processSurvival (V := Fin n) q k - processSurvival (V := Fin n) q (k+1))) =
            ∑ k ∈ Finset.range N,
              ((-processSurvival (V := Fin n) q (k+1)) -
                (-processSurvival (V := Fin n) q k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = -processSurvival (V := Fin n) q N -
              (-processSurvival (V := Fin n) q 0) :=
          Finset.sum_range_sub (fun k => -processSurvival (V := Fin n) q k) N
        _ = processSurvival (V := Fin n) q 0 - processSurvival (V := Fin n) q N := by ring
    have hIco :
        (∑ k ∈ Finset.Ico L U,
          (processSurvival (V := Fin n) q k - processSurvival (V := Fin n) q (k+1))) =
          processSurvival (V := Fin n) q L - processSurvival (V := Fin n) q U := by
      rw [Finset.sum_Ico_eq_sub _ hLU, hRange U, hRange L]
      ring
    calc
      terminalProb (V := Fin n) q L U (fun _ _ => True) =
          ∑ k ∈ Finset.Ico L U, terminalStep (V := Fin n) q k (fun _ _ => 1) := hterminal
      _ = ∑ k ∈ Finset.Ico L U,
            (processSurvival (V := Fin n) q k - processSurvival (V := Fin n) q (k+1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (survival_step (n := n) (m := k) q).symm
      _ = processSurvival (V := Fin n) q L - processSurvival (V := Fin n) q U := hIco
  · intro T hUT
    have hb := h08b q n hq hn T L U hLU hUT (fun _ _ _ => 1)
    have hsample : ∀ x : EdgeTuple (Fin n) T,
        terminalSample (V := Fin n) q L U (fun _ _ _ => 1) x =
          indicator (L < boundedFailure q x ∧ boundedFailure q x ≤ U) := by
      intro x
      simp [terminalSample, indicator, hUT]
    calc
      terminalProb (V := Fin n) q L U (fun _ _ => True) =
          uniformMean (terminalSample (V := Fin n) q L U (fun _ _ _ => 1)) := by
        simpa [terminalProb, indicator] using hb.symm
      _ = uniformProb (fun x : EdgeTuple (Fin n) T =>
            L < boundedFailure q x ∧ boundedFailure q x ≤ U) := by
        unfold uniformProb
        exact uniformMean_congr _ _ hsample

end ThLean.W.S432

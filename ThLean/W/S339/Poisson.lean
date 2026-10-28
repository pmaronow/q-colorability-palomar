import ThLean.BP.S3.Support
import ThLean.BP.S3.Poisson
import ThLean.W.S339.ListMean

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S339
open ThresholdFoundations
open ThLean.BP.S3

universe u

lemma listGraph_ofFn {V : Type u} [Fintype V] {m : ℕ} (x : Fin m → Pair V) :
    listGraph (List.ofFn x) = tupleGraph x := by
  funext e
  change ((List.ofFn x).filter (fun p => p.val = e)).length =
    (Finset.univ.filter (fun i => (x i).val = e)).card
  have hfin : (List.finRange m).toFinset = Finset.univ := by
    ext i
    simp
  rw [← List.countP_eq_length_filter, List.ofFn_eq_map, List.countP_map]
  change List.countP (fun i : Fin m => decide ((x i).val = e)) (List.finRange m) =
    (Finset.univ.filter (fun i => (x i).val = e)).card
  simpa [hfin] using
    ((List.nodup_finRange m).card_eq_countP (P := fun i => (x i).val = e)).symm

lemma weightedListMean_uniform_eq_poissonGraphMean {V : Type u} [Fintype V]
    (z : ℝ) (h : MGraph V → ℝ) :
    weightedListMean z (fun _ : Pair V => 1 / (Fintype.card (Pair V) : ℝ))
      (fun xs => h (listGraph xs)) = poissonGraphMean z h := by
  classical
  simp [weightedListMean, poissonGraphMean, poissonMixture, uniformMean,
    listGraph_ofFn, EdgeTuple, Finset.prod_const]
  apply tsum_congr
  intro k
  congr 1
  rw [← Finset.mul_sum, div_eq_mul_inv]
  ring

lemma pair_nonempty_of_card_ge_two {V : Type u} [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  classical
  let e := Fintype.equivFin V
  let a : V := e.symm ⟨0, by omega⟩
  let b : V := e.symm ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hh := congrArg e h
    simp [a, b] at hh
  refine ⟨⟨s(a,b), ?_⟩⟩
  intro c hc
  rcases Sym2.eq_iff.mp hc with ⟨hac, hbc⟩ | ⟨hac, hbc⟩
  · exact hab (hac.trans hbc.symm)
  · exact hab (hac.trans hbc.symm)

lemma cellMass_equiv_uniform {E : Type u} [Fintype E]
    (N : ℕ) (e : E ≃ Fin N) (j : Fin N) :
    ThLean.BP.S3.cellMass (fun _ : E => 1 / (N : ℝ)) e j = 1 / (N : ℝ) := by
  classical
  change (∑ x : E, if e x = j then 1 / (N : ℝ) else 0) = _
  rw [Equiv.sum_comp e (fun j' => if j' = j then 1 / (N : ℝ) else 0)]
  simp

lemma list_eq_replicate_of_forall_mem_eq {α : Type*} [DecidableEq α]
    (xs : List α) (a : α) (h : ∀ b ∈ xs, b = a) :
    xs = List.replicate xs.length a := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
      have hb : b = a := h b (by simp)
      subst b
      have hbs : ∀ c ∈ bs, c = a := by
        intro c hc
        exact h c (by simp [hc])
      rw [ih hbs]
      simp only [List.length_cons, List.length_replicate]
      rw [List.replicate_succ]

lemma listGraph_loop_zero {V : Type u} [Fintype V] (w : List (Pair V)) (v : V) :
    listGraph w (s(v,v)) = 0 := by
  induction w with
  | nil => simp [listGraph]
  | cons p ps ih =>
      have hp : p.val ≠ s(v,v) := p.property v
      simpa [listGraph, hp] using ih

lemma splitSublist_length_eq_listGraph {V : Type u} [Fintype V]
    (N : ℕ) (ρ : Pair V ≃ Fin N) (j : Fin N) (w : List (Pair V)) :
    (ThresholdFoundations.splitSublist ρ j w).length =
      listGraph w (ρ.symm j).val := by
  classical
  let p : Pair V := ρ.symm j
  have hpred : ∀ q : Pair V, (ρ q = j) ↔ q.val = p.val := by
    intro q
    constructor
    · intro hq
      have heq : q = p := ρ.injective (by simpa [p] using hq)
      simpa [heq]
    · intro hq
      have heq : q = p := Subtype.ext hq
      simpa [heq, p]
  change (w.filter (fun q => decide (ρ q = j))).length =
    (w.filter (fun q => decide (q.val = p.val))).length
  congr 1
  apply List.filter_congr
  intro q hq
  simp [hpred q]

lemma splitSublist_replicate_iff {V : Type u} [Fintype V]
    (N : ℕ) (ρ : Pair V ≃ Fin N) (G : MGraph V) (hG : Loopless G) (w : List (Pair V)) :
    (∀ j, ThresholdFoundations.splitSublist ρ j w =
      List.replicate (G (ρ.symm j).val) (ρ.symm j)) ↔ listGraph w = G := by
  classical
  constructor
  · intro hs
    funext e
    by_cases hloop : ∃ v, e = s(v,v)
    · rcases hloop with ⟨v, rfl⟩
      change listGraph w (s(v,v)) = G (s(v,v))
      exact (listGraph_loop_zero w v).trans (hG v).symm
    · let p : Pair V := ⟨e, by
        intro v hv
        exact hloop ⟨v, hv⟩⟩
      have hlen := splitSublist_length_eq_listGraph N ρ (ρ p) w
      have h := hs (ρ p)
      rw [h, List.length_replicate] at hlen
      simpa [p] using hlen.symm
  · intro hg j
    let p : Pair V := ρ.symm j
    have hmem : ∀ q ∈ ThresholdFoundations.splitSublist ρ j w, q = p := by
      intro q hq
      have hq' : ρ q = j := by
        have hq'' : q ∈ w ∧ ρ q = j := by
          simpa [ThresholdFoundations.splitSublist] using hq
        exact hq''.2
      apply ρ.injective
      simpa [p] using hq'
    rw [list_eq_replicate_of_forall_mem_eq _ p hmem]
    rw [splitSublist_length_eq_listGraph N ρ j w, hg]


lemma independentMass_eq_pairProduct {V : Type u} [Fintype V]
    (h31 : ThLean.BP.S3.S3_31Statement) (rate : ℝ) (hrate : 0 ≤ rate)
    (G : MGraph V) (hG : Loopless G) :
    independentPoissonGraphMass (ThLean.BP.S3.pairRate rate) G =
      ∏ p : Pair V, poissonWeight rate (G p.val) := by
  classical
  unfold independentPoissonGraphMass
  have hcoord (e : Sym2 V) :
      poissonWeight (ThLean.BP.S3.pairRate rate e) (G e) =
        if e ∈ completeEdges then poissonWeight rate (G e) else 1 := by
    by_cases he : e ∈ completeEdges
    · have hnonloop : ¬ ∃ v, e = s(v,v) := by
        simpa [completeEdges] using he
      simp [ThLean.BP.S3.pairRate, he, hnonloop]
    · have hloop : ∃ v, e = s(v,v) := by
        simpa [completeEdges] using he
      rcases hloop with ⟨v, rfl⟩
      have hw : poissonWeight 0 (G (s(v,v))) = 1 := by
        rw [hG v]
        exact (h31 0 (by norm_num)).2.2.2.2.1 0
      have hw0 : poissonWeight 0 0 = 1 := by
        rw [← hG v]
        exact hw
      simpa [ThLean.BP.S3.pairRate, completeEdges, hG v] using hw0
  calc
    (∏ e : Sym2 V, poissonWeight (ThLean.BP.S3.pairRate rate e) (G e)) =
        ∏ e : Sym2 V, if e ∈ completeEdges then poissonWeight rate (G e) else 1 := by
          apply Finset.prod_congr rfl
          intro e he
          exact hcoord e
    _ = ∏ e ∈ completeEdges, poissonWeight rate (G e) := by
          rw [← Finset.prod_filter]
          simp
    _ = ∏ p : Pair V, poissonWeight rate (G p.val) := by
          simpa [Pair, completeEdges] using
            (Finset.prod_subtype (completeEdges (V := V))
              (fun e => by simp [completeEdges]) (fun e => poissonWeight rate (G e)))

lemma poissonGraph_pointMass_loopless_of_s35a {V : Type u} [Fintype V]
    (h31 : ThLean.BP.S3.S3_31Statement)
    (h35a : ThLean.BP.S3.S3_35aStatement.{u})
    (hV : 2 ≤ Fintype.card V) (t : ℝ) (ht : 0 ≤ t)
    (G : MGraph V) (hG : Loopless G) :
    poissonGraphMean t (fun H => indicator (H = G)) =
      independentPoissonGraphMass
        (ThLean.BP.S3.pairRate (t / Fintype.card (Pair V))) G := by
  classical
  letI : Nonempty (Pair V) := pair_nonempty_of_card_ge_two hV
  let N : ℕ := Fintype.card (Pair V)
  have hN : 0 < N := Fintype.card_pos
  let ρ : Pair V ≃ Fin N := Fintype.equivFin (Pair V)
  let ν : Pair V → ℝ := fun _ => 1 / (N : ℝ)
  have hν : IsProbabilityVector ν := by
    constructor
    · intro p
      dsimp [ν]
      positivity
    · calc
        (∑ p : Pair V, ν p) = (N : ℝ) * (1 / (N : ℝ)) := by simp [ν, N]
        _ = 1 := by
          have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
          field_simp
  let ys : Fin N → List (Pair V) := fun j =>
    List.replicate (G (ρ.symm j).val) (ρ.symm j)
  have hys : ∀ j, ∀ p ∈ ys j, ρ p = j := by
    intro j p hp
    have hp' : p = ρ.symm j := by
      have hp'' : G (ρ.symm j).val ≠ 0 ∧ p = ρ.symm j := by
        simpa [ys] using hp
      exact hp''.2
    rw [hp']
    exact ρ.apply_symm_apply j
  have hpos : ∀ j, 0 < ThLean.BP.S3.cellMass ν ρ j := by
    intro j
    rw [cellMass_equiv_uniform N ρ j]
    have hNr : (N : ℝ) > 0 := by exact_mod_cast hN
    positivity
  have hsplit := h35a (Pair V) ν N ρ t hν ht hpos ys hys
  have hprod :
      (∏ j : Fin N, poissonListMass (t * ThLean.BP.S3.cellMass ν ρ j)
        (fun p => ν p / ThLean.BP.S3.cellMass ν ρ j) (ys j)) =
      ∏ p : Pair V, poissonWeight (t / (N : ℝ)) (G p.val) := by
    calc
      _ = ∏ j : Fin N, poissonWeight (t / (N : ℝ)) (G (ρ.symm j).val) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [cellMass_equiv_uniform N ρ j]
        have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
        simp [poissonListMass, ys, ν, hNr]
        congr 1
      _ = ∏ p : Pair V, poissonWeight (t / (N : ℝ)) (G p.val) := by
        exact Equiv.prod_comp ρ.symm
          (fun p => poissonWeight (t / (N : ℝ)) (G p.val))
  have hevent : ∀ w : List (Pair V),
      (∀ j, ThresholdFoundations.splitSublist ρ j w = ys j) ↔ listGraph w = G := by
    intro w
    simpa [ys] using splitSublist_replicate_iff N ρ G hG w
  calc
    poissonGraphMean t (fun H => indicator (H = G)) =
        weightedListMean t ν (fun w => indicator (listGraph w = G)) :=
      (weightedListMean_uniform_eq_poissonGraphMean t (fun H => indicator (H = G))).symm
    _ = weightedListMean t ν
        (fun w => indicator (∀ j, ThresholdFoundations.splitSublist ρ j w = ys j)) := by
      congr 1
      funext w
      apply congrArg indicator
      exact propext (hevent w).symm
    _ = ∏ j : Fin N, poissonListMass (t * ThLean.BP.S3.cellMass ν ρ j)
        (fun p => ν p / ThLean.BP.S3.cellMass ν ρ j) (ys j) := hsplit
    _ = ∏ p : Pair V, poissonWeight (t / (N : ℝ)) (G p.val) := hprod
    _ = independentPoissonGraphMass
        (ThLean.BP.S3.pairRate (t / Fintype.card (Pair V))) G := by
      symm
      simpa [N] using
        independentMass_eq_pairProduct h31 (t / (N : ℝ)) (by positivity) G hG

lemma tupleGraph_loop_zero {V : Type u} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (v : V) : tupleGraph x (s(v,v)) = 0 := by
  classical
  have hfilter :
      Finset.univ.filter (fun i : Fin m => (x i).val = s(v,v)) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
    simp [(x i).property v]
  simp [tupleGraph, hfilter]

lemma poissonGraph_pointMass_of_s35a {V : Type u} [Fintype V]
    (h31 : ThLean.BP.S3.S3_31Statement)
    (h35a : ThLean.BP.S3.S3_35aStatement.{u})
    (hV : 2 ≤ Fintype.card V) (t : ℝ) (ht : 0 ≤ t) (G : MGraph V) :
    poissonGraphMean t (fun H => indicator (H = G)) =
      independentPoissonGraphMass
        (ThLean.BP.S3.pairRate (t / Fintype.card (Pair V))) G := by
  classical
  by_cases hG : Loopless G
  · exact poissonGraph_pointMass_loopless_of_s35a h31 h35a hV t ht G hG
  · unfold Loopless at hG
    push_neg at hG
    rcases hG with ⟨v, hv⟩
    have hvpos : 0 < G (s(v,v)) := Nat.pos_of_ne_zero hv
    have hnoTuple : ∀ m (x : EdgeTuple V m), tupleGraph x ≠ G := by
      intro m x hx
      have hcoord := congrFun hx (s(v,v))
      rw [tupleGraph_loop_zero] at hcoord
      exact hv hcoord.symm
    have hleft : poissonGraphMean t (fun H => indicator (H = G)) = 0 := by
      simp [poissonGraphMean, poissonMixture, uniformMean, indicator, hnoTuple]
    have hweight : poissonWeight 0 (G (s(v,v))) = 0 := by
      have h := (h31 0 (by norm_num)).2.2.2.2.1 (G (s(v,v)))
      rw [if_neg (Nat.ne_of_gt hvpos)] at h
      exact h
    have hright : independentPoissonGraphMass
        (ThLean.BP.S3.pairRate (t / Fintype.card (Pair V))) G = 0 := by
      unfold independentPoissonGraphMass
      apply Finset.prod_eq_zero (Finset.mem_univ (s(v,v)))
      simpa [ThLean.BP.S3.pairRate] using hweight
    rw [hleft, hright]

end ThLean.W.S339

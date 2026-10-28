import ThLean.BP.S6.Potential

noncomputable section
open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S633

private theorem tupleGraph_takePrefix {n m M : ℕ} (hm : m ≤ M)
    (x : Hist n M) : tupleGraph (takePrefix hm x) = tuplePrefix x m := by
  classical
  letI : DecidableEq (Fin n) := Classical.decEq _
  funext e
  unfold tupleGraph tuplePrefix
  refine Finset.card_bij
    (fun i _ => (⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩ : Fin M)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    constructor
    · exact i.isLt
    · change (x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩).val = e
      exact hi
  · intro a ha b hb h
    apply Fin.ext
    exact congrArg (fun z : Fin M => z.val) h
  · intro b hb
    have hb'' := (Finset.mem_filter.mp hb).2
    have hbval : b.val < m := hb''.1
    have hbe : (x b).val = e := hb''.2
    refine ⟨⟨b.val, hbval⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (x ⟨b.val, Nat.lt_of_lt_of_le hbval hm⟩).val = e
      exact hbe
    · apply Fin.ext
      rfl

private theorem degree_tupleGraph_le {n m : ℕ} (x : Hist n m) (u : Fin n) :
    degree (tupleGraph x) u ≤ m := by
  classical
  have hle : degree (tupleGraph x) u ≤ edgeCount (tupleGraph x) := by
    unfold degree edgeCount
    apply Finset.sum_le_sum
    intro e he
    by_cases ht : Touches u e <;> simp [ht]
  calc
    degree (tupleGraph x) u ≤ edgeCount (tupleGraph x) := hle
    _ = m := by
      unfold edgeCount tupleGraph
      simpa using (Finset.sum_card_fiberwise_eq_card_filter
        (s := Finset.univ) (t := Finset.univ) (g := fun i : Fin m => (x i).val))

private theorem rootDegreeTail (n m j : ℕ) (hn : 3 ≤ n) (u : Fin n)
    (h30a : ThLean.BP.S6.S6_30aStatement) :
    uniformProb (fun x : Hist n m => j ≤ degree (tupleGraph x) u) =
      ThLean.BP.S6.binomialTail m (2 / (n : ℝ)) j := by
  classical
  have hpoint (x : Hist n m) :
      indicator (j ≤ degree (tupleGraph x) u) =
        ∑ k ∈ Finset.range (m + 1),
          if j ≤ k then indicator (degree (tupleGraph x) u = k) else 0 := by
    have hsingle (d : ℕ) (hd : d ≤ m) :
        indicator (j ≤ d) =
          ∑ k ∈ Finset.range (m + 1),
            if j ≤ k then indicator (d = k) else 0 := by
      by_cases hj : j ≤ d
      · rw [indicator, if_pos hj]
        rw [Finset.sum_eq_single d]
        · simp [indicator, hj]
        · intro k hk hkd
          have hdk : d ≠ k := Ne.symm hkd
          simp [indicator, hdk]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr (by omega))).elim
      · rw [indicator, if_neg hj]
        symm
        apply Finset.sum_eq_zero
        intro k hk
        by_cases hjk : j ≤ k
        · have hdk : d ≠ k := by
            intro h
            subst k
            exact hj hjk
          simp [hjk, hdk, indicator]
        · simp [hjk]
    exact hsingle _ (degree_tupleGraph_le x u)
  calc
    uniformProb (fun x : Hist n m => j ≤ degree (tupleGraph x) u) =
        uniformMean (fun x : Hist n m =>
          ∑ k ∈ Finset.range (m + 1),
            if j ≤ k then indicator (degree (tupleGraph x) u = k) else 0) := by
      unfold uniformProb
      congr 1
      funext x
      exact hpoint x
    _ = ∑ k ∈ Finset.range (m + 1),
        if j ≤ k then uniformProb
          (fun x : Hist n m => degree (tupleGraph x) u = k) else 0 := by
      change (∑ x : Hist n m, ∑ k ∈ Finset.range (m + 1),
          if j ≤ k then indicator (degree (tupleGraph x) u = k) else 0) /
          (Fintype.card (Hist n m) : ℝ) =
        ∑ k ∈ Finset.range (m + 1), if j ≤ k then
          (∑ x : Hist n m, indicator (degree (tupleGraph x) u = k)) /
            (Fintype.card (Hist n m) : ℝ) else 0
      rw [div_eq_mul_inv, Finset.sum_comm, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hjk : j ≤ k <;> simp [hjk, div_eq_mul_inv, Finset.sum_mul]
    _ = ThLean.BP.S6.binomialTail m (2 / (n : ℝ)) j := by
      simp only [ThLean.BP.S6.binomialTail, ThresholdFoundations.binomialTail]
      simp_rw [h30a n m _ hn u]
      simp [binomialMass, Nat.cast_le]

theorem S6_31aStatement_of_deps
    (h01a : ThLean.BP.S6.S6_01aStatement)
    (h01b : ThLean.BP.S6.S6_01bStatement)
    (h05 : ThLean.BP.S6.S6_05Statement)
    (h30a : ThLean.BP.S6.S6_30aStatement)
    (h30b : ThLean.BP.S6.S6_30bStatement) :
    ThLean.BP.S6.S6_31aStatement := by
  intro n q M j hn hq hj u
  let T : Hist n M → WithTop ℕ := degreeStart (M := M) u j
  let hrules := h01a (Hist n M)
  let hactivation := h30b n q M j hn hq hj u
  have hsum :
      uniformMean (stoppedOccupation q u T) =
        ∑ m ∈ Finset.range M, uniformMean (fun x : Hist n M =>
          if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
          then beta q (tuplePrefix x m) u else 0) := by
    unfold stoppedOccupation uniformMean
    change (∑ x : Hist n M, ∑ m ∈ Finset.range M,
          if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
          then beta q (tuplePrefix x m) u else 0) /
          (Fintype.card (Hist n M) : ℝ) =
        ∑ m ∈ Finset.range M,
          (∑ x : Hist n M,
            if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
            then beta q (tuplePrefix x m) u else 0) /
              (Fintype.card (Hist n M) : ℝ)
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_comm, Finset.sum_mul]
  have hterm (m : ℕ) (hm : m < M) :
      uniformMean (fun x : Hist n M =>
        if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
        then beta q (tuplePrefix x m) u else 0) =
      rootGeMean n q m j u := by
    have hmle : m ≤ M := Nat.le_of_lt hm
    have hgraph (x : Hist n M) := tupleGraph_takePrefix hmle x
    have hpoint (x : Hist n M) :
        (if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
          then beta q (tuplePrefix x m) u else 0) =
        indicator (j ≤ degree (tupleGraph (takePrefix hmle x)) u) *
          beta q (tupleGraph (takePrefix hmle x)) u := by
      have hdegree := (hactivation.2.1 x m)
      by_cases hd : j ≤ degree (tuplePrefix x m) u
      · have hdGraph : j ≤ degree (tupleGraph (takePrefix hmle x)) u := by
          simpa [hgraph x] using hd
        have htime : T x ≤ (m : WithTop ℕ) := hdegree.mpr hd
        by_cases hc : Colorable q (tuplePrefix x m)
        · simp [indicator, hd, hdGraph, htime, hc, hgraph x]
        · rcases h05 n q hn hq (tuplePrefix x m) u with
            ⟨_, _, _, _, _, _, _, _, hnotcolor⟩
          have hzero : beta q (tuplePrefix x m) u = 0 := (hnotcolor hc).2
          simp [indicator, hd, hdGraph, htime, hc, hzero, hgraph x]
      · have htime : ¬ T x ≤ (m : WithTop ℕ) := fun h => hd (hdegree.mp h)
        simp [indicator, hd, htime, hgraph x]
    have hpref := (h01b n hn).1 m M hmle
      (fun y : Hist n m => indicator (j ≤ degree (tupleGraph y) u) * beta q (tupleGraph y) u)
    calc
      uniformMean (fun x : Hist n M =>
          if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
          then beta q (tuplePrefix x m) u else 0) =
          uniformMean (fun x : Hist n M =>
            indicator (j ≤ degree (tupleGraph (takePrefix hmle x)) u) *
              beta q (tupleGraph (takePrefix hmle x)) u) := by
        congr 1
        funext x
        exact hpoint x
      _ = uniformMean (fun y : Hist n m =>
          indicator (j ≤ degree (tupleGraph y) u) * beta q (tupleGraph y) u) := hpref
      _ = rootGeMean n q m j u := rfl
  constructor
  · rw [hsum]
    apply Finset.sum_congr rfl
    intro m hm
    exact (hterm m (Finset.mem_range.mp hm)).symm
  · have hm : M - 1 ≤ M := by omega
    have hactive : uniformProb (activeStart q T) ≤
        uniformProb (fun x : Hist n M =>
          j ≤ degree (tuplePrefix x (M - 1)) u) := by
      apply hrules.mono
      intro x
      by_cases ha : activeStart q T x
      · have hdeg := (hactivation.2.2.1 x ha).2
        simp [indicator, ha, hdeg]
      · by_cases hd : j ≤ degree (tuplePrefix x (M - 1)) u <;>
          simp [indicator, ha, hd]
    have hprefix :
        uniformProb (fun x : Hist n M =>
          j ≤ degree (tuplePrefix x (M - 1)) u) =
        uniformProb (fun y : Hist n (M - 1) =>
          j ≤ degree (tupleGraph y) u) := by
      have htransport := (h01b n hn).1 (M - 1) M hm
        (fun y : Hist n (M - 1) => indicator (j ≤ degree (tupleGraph y) u))
      unfold uniformProb
      calc
        uniformMean (fun x : Hist n M =>
            indicator (j ≤ degree (tuplePrefix x (M - 1)) u)) =
          uniformMean (fun x : Hist n M =>
            indicator (j ≤ degree (tupleGraph (takePrefix hm x)) u)) := by
              congr 1
              funext x
              rw [tupleGraph_takePrefix hm x]
        _ = uniformMean (fun y : Hist n (M - 1) =>
            indicator (j ≤ degree (tupleGraph y) u)) := htransport
    calc
      uniformProb (activeStart q T) ≤
          uniformProb (fun x : Hist n M =>
            j ≤ degree (tuplePrefix x (M - 1)) u) := hactive
      _ = uniformProb (fun y : Hist n (M - 1) =>
          j ≤ degree (tupleGraph y) u) := hprefix
      _ = ThLean.BP.S6.binomialTail (M - 1) (2 / (n : ℝ)) j :=
          rootDegreeTail n (M - 1) j hn u h30a

end ThLean.W.S633

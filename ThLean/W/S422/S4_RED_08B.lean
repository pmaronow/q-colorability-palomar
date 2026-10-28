import ThLean.W.S422.TerminalHelpers

noncomputable section
open scoped BigOperators
namespace ThLean.W.S422
open ThresholdFoundations ThLean.BP.S4

def terminalSummand {V : Type} [Fintype V] {T : ℕ}
    (q : ℕ) (F : ℕ → MGraph V → Pair V → ℝ)
    (x : EdgeTuple V T) (k : ℕ) : ℝ := by
  classical
  exact if hk : k < T then
      if Colorable q (tuplePrefix x k) ∧
          ¬ Colorable q (tuplePrefix x (k+1)) then
        F (k+1) (tuplePrefix x k) (x ⟨k, hk⟩)
      else 0
    else 0

theorem terminalSample_eq_sum {V : Type} [Fintype V] {T : ℕ}
    (q L U : ℕ) (F : ℕ → MGraph V → Pair V → ℝ)
    (hUT : U ≤ T) (hq : 0 < q) (x : EdgeTuple V T) :
    terminalSample q L U F x =
      ∑ k ∈ Finset.Ico L U, terminalSummand q F x k := by
  classical
  let c := cappedLast q x
  have hcap : cappedLast q x = c := rfl
  have hbf : boundedFailure q x = c+1 := by simp [boundedFailure, c]
  by_cases hbranch : L < boundedFailure q x ∧
      boundedFailure q x ≤ U ∧ U ≤ T
  · have hct : c < T := by rw [hbf] at hbranch; omega
    have htrans := cap_transition x hq hct hcap
    have hcI : c ∈ Finset.Ico L U := by
      simp only [Finset.mem_Ico]
      rw [hbf] at hbranch
      omega
    have hbranch' : L < c+1 ∧ c+1 ≤ U ∧ U ≤ T := by
      simpa [hbf] using hbranch
    have hsample : terminalSample q L U F x =
        F (c+1) (tuplePrefix x c) (x ⟨c, hct⟩) := by
      simp [terminalSample, hbf, hbranch', boundedLast, c]
    have hsum :
        (∑ k ∈ Finset.Ico L U, terminalSummand q F x k) =
          F (c+1) (tuplePrefix x c) (x ⟨c, hct⟩) := by
      calc
        (∑ k ∈ Finset.Ico L U, terminalSummand q F x k) =
            terminalSummand q F x c := by
          apply Finset.sum_eq_single c
          · intro j hj hjne
            have hjI := Finset.mem_Ico.mp hj
            have hjt : j < T := by omega
            by_cases htj : Colorable q (tuplePrefix x j) ∧
                ¬ Colorable q (tuplePrefix x (j+1))
            · have hcount := transition_count x hjt htj
              have hjc : j = c := by omega
              exact False.elim (hjne hjc)
            · simp [terminalSummand, hjt, htj]
          · intro hnot
            exact False.elim (hnot hcI)
        _ = F (c+1) (tuplePrefix x c) (x ⟨c, hct⟩) := by
          simp [terminalSummand, hct, htrans]
    exact hsample.trans hsum.symm
  · have hsum :
        (∑ k ∈ Finset.Ico L U, terminalSummand q F x k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjI := Finset.mem_Ico.mp hj
      by_cases htj : Colorable q (tuplePrefix x j) ∧
          ¬ Colorable q (tuplePrefix x (j+1))
      · have hjt : j < T := by omega
        have hcount := transition_count x hjt htj
        have hbfj : boundedFailure q x = j+1 := by
          simp [boundedFailure, hcount]
        have hcontr : L < boundedFailure q x ∧
            boundedFailure q x ≤ U ∧ U ≤ T := by
          rw [hbfj]
          exact ⟨by omega, by omega, hUT⟩
        exact False.elim (hbranch hcontr)
      · simp [terminalSummand, htj]
    simp [terminalSample, hbranch, hsum]

theorem terminalSummand_mean {V : Type} [Fintype V] [Fintype (Pair V)]
    [Nonempty (Pair V)]
    {T : ℕ} (q k : ℕ) (F : ℕ → MGraph V → Pair V → ℝ)
    (hk : k < T) : by
    classical
    exact (uniformMean (fun x : EdgeTuple V T => terminalSummand q F x k) =
      uniformMean (fun y : EdgeTuple V k => uniformMean (fun e : Pair V =>
        if Colorable q (tupleGraph y) ∧
            ¬ Colorable q (addPair (tupleGraph y) e)
        then F (k+1) (tupleGraph y) e else 0)))
  := by
  classical
  have hrT : k+1 ≤ T := by omega
  have hprefix : ∀ x : EdgeTuple V T,
      terminalSummand q F x k = terminalSummand q F (restrictTuple hrT x) k := by
    intro x
    have hp0 := tuplePrefix_restrict_consistency x hrT (by omega : k ≤ k+1)
    have hp1 := tuplePrefix_restrict_consistency x hrT (by omega : k+1 ≤ k+1)
    have he : x ⟨k, hk⟩ = restrictTuple hrT x ⟨k, by omega⟩ := by rfl
    simp [terminalSummand, hk, hp0, hp1, he]
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hrT
  subst T
  have hbase := uniformMean_prefix (E := Pair V) (r := k+1)
    (s := s) (fun z : EdgeTuple V (k+1) => terminalSummand q F z k)
  have hbase' :
      uniformMean (fun x : EdgeTuple V ((k+1)+s) =>
        terminalSummand q F (fun (i : Fin (k+1)) => x ⟨i.val, by omega⟩) k) =
      uniformMean (fun z : EdgeTuple V (k+1) => terminalSummand q F z k) := by
    simpa [restrictTuple] using hbase
  have hproj (x : EdgeTuple V ((k+1)+s)) :
      restrictTuple hrT x =
        (fun (i : Fin (k+1)) => x ⟨i.val, by omega⟩) := by
    funext i
    rfl
  calc
    uniformMean (fun x : EdgeTuple V ((k+1)+s) => terminalSummand q F x k) =
        uniformMean (fun x : EdgeTuple V ((k+1)+s) =>
          terminalSummand q F (fun (i : Fin (k+1)) => x ⟨i.val, by omega⟩) k) := by
            congr 1
            funext x
            rw [← hproj x]
            exact hprefix x
    _ = uniformMean (fun z : EdgeTuple V (k+1) => terminalSummand q F z k) := hbase'
    _ = uniformMean (fun z : EdgeTuple V (k+1) =>
          if Colorable q (tupleGraph (fun i => z i.castSucc)) ∧
              ¬ Colorable q (addPair (tupleGraph (fun i => z i.castSucc))
                (z (Fin.last k)))
          then F (k+1) (tupleGraph (fun i => z i.castSucc)) (z (Fin.last k))
          else 0) := by
            congr 1
            funext z
            have hp := tuplePrefix_snoc z
            have he : z ⟨k, by omega⟩ = z (Fin.last k) := by
              apply congrArg z
              apply Fin.ext
              rfl
            simp [terminalSummand, hp.1, hp.2, he]
    _ = uniformMean (fun y : EdgeTuple V k => uniformMean (fun e : Pair V =>
          if Colorable q (tupleGraph y) ∧
              ¬ Colorable q (addPair (tupleGraph y) e)
          then F (k+1) (tupleGraph y) e else 0)) := by
            exact uniformMean_snoc_prod k (fun y e =>
              if Colorable q (tupleGraph y) ∧
                  ¬ Colorable q (addPair (tupleGraph y) e)
              then F (k+1) (tupleGraph y) e else 0)

private lemma uniformMean_sum {A I : Type} [Fintype A]
    (s : Finset I) (f : A → I → ℝ) :
    uniformMean (fun a => ∑ i ∈ s, f a i) =
      ∑ i ∈ s, uniformMean (fun a => f a i) := by
  classical
  unfold uniformMean
  calc
    (∑ a, ∑ i ∈ s, f a i) / (Fintype.card A : ℝ) =
        (∑ i ∈ s, ∑ a, f a i) / (Fintype.card A : ℝ) := by
          congr 1
          exact Finset.sum_comm
    _ = ∑ i ∈ s, (∑ a, f a i) / (Fintype.card A : ℝ) := by
          rw [Finset.sum_div]

set_option maxHeartbeats 0 in
theorem S4_RED_08BStatement_holds : ThLean.BP.S4.S4_RED_08BStatement := by
  intro q n hq hn T L U hLU hUT F
  let iNatPair : Fintype (Pair (Fin n)) := by infer_instance
  letI : Fintype (Pair (Fin n)) := iNatPair
  let iNatTuple : Fintype (EdgeTuple (Fin n) T) := by infer_instance
  classical
  let iClassPair : Fintype (Pair (Fin n)) := by
    let iV : Fintype (Fin n) := inferInstance
    letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable _
    letI : DecidableEq (Sym2 (Fin n)) := Sym2.instDecidableEq
    letI : Fintype (Sym2 (Fin n)) := @Sym2.instFintype (Fin n) iV
    letI : DecidablePred (fun e : Sym2 (Fin n) =>
        ∀ v : Fin n, e ≠ s(v,v)) := fun e => Fintype.decidableForallFintype
    exact Subtype.fintype _
  let iClassTuple : Fintype (EdgeTuple (Fin n) T) := by
    letI : Fintype (Pair (Fin n)) := iClassPair
    infer_instance
  let iPiTuple : Fintype (EdgeTuple (Fin n) T) :=
    @Pi.instFintype (Fin T) (fun _ : Fin T => Pair (Fin n))
      (inferInstance : DecidableEq (Fin T))
      (inferInstance : Fintype (Fin T))
      (fun _ => iClassPair)
  have hOuter :
      @uniformMean (EdgeTuple (Fin n) T) iNatTuple (terminalSample q L U F) =
        @uniformMean (EdgeTuple (Fin n) T) iClassTuple (terminalSample q L U F) :=
    uniformMean_fintype_indep iNatTuple iClassTuple _
  letI : Fintype (Pair (Fin n)) := iClassPair
  letI : Fintype (EdgeTuple (Fin n) T) := iClassTuple
  haveI : Nonempty (Pair (Fin n)) := pair_nonempty_fin (by omega)
  change @uniformMean (EdgeTuple (Fin n) T) iNatTuple (terminalSample q L U F) =
    terminalReal q L U F
  calc
    @uniformMean (EdgeTuple (Fin n) T) iNatTuple (terminalSample q L U F) =
        @uniformMean (EdgeTuple (Fin n) T) iClassTuple (terminalSample q L U F) := hOuter
    _ = @uniformMean (EdgeTuple (Fin n) T) iClassTuple (fun x : EdgeTuple (Fin n) T =>
          ∑ k ∈ Finset.Ico L U, terminalSummand q F x k) := by
            congr 1
            funext x
            exact terminalSample_eq_sum q L U F hUT (by omega) x
    _ = ∑ k ∈ Finset.Ico L U,
          uniformMean (fun x : EdgeTuple (Fin n) T => terminalSummand q F x k) :=
            uniformMean_sum (Finset.Ico L U)
              (fun x : EdgeTuple (Fin n) T => terminalSummand q F x)
    _ = terminalReal q L U F := by
          unfold terminalReal
          apply Finset.sum_congr rfl
          intro k hk
          have hkT : k < T := by
            have hi := Finset.mem_Ico.mp hk
            omega
          have hterm := @terminalSummand_mean (Fin n)
            (inferInstance : Fintype (Fin n)) iClassPair
            (inferInstance : Nonempty (Pair (Fin n))) T q k F hkT
          have htupleMean := uniformMean_fintype_indep iPiTuple iClassTuple
            (fun x : EdgeTuple (Fin n) T => terminalSummand q F x k)
          exact htupleMean.symm.trans hterm

end ThLean.W.S422

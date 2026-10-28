import ThLean.BP.SA.Transfer
import ThLean.W.BR01.PairBridge

set_option maxHeartbeats 5000000

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA65
open ThresholdFoundations
open ThLean.BP.SA

private def tupleSupport {V : Type*} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.image (fun i => (x i).val)

private theorem tupleSupport_eq_edgeSupport {V : Type*} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) : tupleSupport x = edgeSupport (tupleGraph x) := by
  unfold tupleSupport edgeSupport tupleGraph
  ext e
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    apply Finset.card_pos.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  · intro he
    rcases Finset.card_pos.mp he with ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩

private def pairSubsetEquiv {V : Type*} [Fintype V]
    (E : Finset (Sym2 V)) (hE : E ⊆ completeEdges (V := V)) :
    {p : Pair V // p.val ∈ E} ≃ {e // e ∈ E} where
  toFun p := ⟨p.val.val, p.property⟩
  invFun e := ⟨⟨e.val, by
    intro v hv
    have he := hE e.property
    exact (Finset.mem_filter.mp he).2 v hv⟩, e.property⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro e
    apply Subtype.ext
    rfl

private def pairCompleteEquiv {V : Type*} [Fintype V] :
    Pair V ≃ {e : Sym2 V // e ∈ completeEdges (V := V)} where
  toFun p := ⟨p.val, by
    change p.val ∈ Finset.univ.filter (fun e : Sym2 V => ∀ v, e ≠ s(v, v))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.property⟩⟩
  invFun e := ⟨e.val, (Finset.mem_filter.mp e.property).2⟩
  left_inv := by intro p; apply Subtype.ext; rfl
  right_inv := by intro e; apply Subtype.ext; rfl

private abbrev tupleFiber {V : Type*} [Fintype V] [Fintype (Pair V)] (m : ℕ)
    (E : Finset (Sym2 V)) :=
  {x : EdgeTuple V m // DistinctPrefix x ∧ tupleSupport x = E}

private def tupleOrderEquiv {V : Type*} [Fintype V] [Fintype (Pair V)]
    (m : ℕ) (E : Finset (Sym2 V))
    (hE : E ⊆ completeEdges (V := V)) :
    tupleFiber m E ≃ (Fin m ≃ {p : Pair V // p.val ∈ E}) := by
  let f (x : tupleFiber m E) (i : Fin m) : {p : Pair V // p.val ∈ E} :=
    ⟨x.1 i, by
      have hi : (x.1 i).val ∈ tupleSupport x.1 :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rw [x.2.2] at hi
      exact hi⟩
  let ordering (x : tupleFiber m E) : Fin m ≃ {p : Pair V // p.val ∈ E} :=
    Equiv.ofBijective (f x) (by
      constructor
      · intro i j hij
        apply x.2.1
        exact congrArg Subtype.val hij
      · intro p
        have hp : p.val.val ∈ tupleSupport x.1 := by
          rw [x.2.2]
          exact p.property
        rcases Finset.mem_image.mp hp with ⟨i, -, hi⟩
        refine ⟨i, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hi)
  refine
    { toFun := ordering
      invFun := fun e => ⟨(fun i => (e i).val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro i j hij
      apply e.injective
      apply Subtype.ext
      exact hij
    · apply Finset.ext
      intro z
      constructor
      · intro hz
        rcases Finset.mem_image.mp hz with ⟨i, -, hi⟩
        have he := (e i).property
        simpa [hi] using he
      · intro hz
        let p : {p : Pair V // p.val ∈ E} := (pairSubsetEquiv E hE).symm ⟨z, hz⟩
        obtain ⟨i, hi⟩ := e.surjective p
        apply Finset.mem_image.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        change ((e i).val).val = z
        rw [hi]
        rfl
  · intro x
    apply Subtype.ext
    funext i
    rfl
  · intro e
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

private theorem tupleFiber_card {V : Type*} [Fintype V] [Fintype (Pair V)]
    (m : ℕ) (E : Finset (Sym2 V))
    (hE : E ⊆ completeEdges (V := V)) (hcard : E.card = m) :
    Fintype.card (tupleFiber m E) = Nat.factorial m := by
  classical
  let T := {p : Pair V // p.val ∈ E}
  have hT : Fintype.card T = m := by
    calc
      Fintype.card T = Fintype.card {e // e ∈ E} :=
        Fintype.card_congr (pairSubsetEquiv E hE)
      _ = E.card := Fintype.card_coe E
      _ = m := hcard
  let e : Fin m ≃ T := Fintype.equivOfCardEq (by simpa using hT.symm)
  calc
    Fintype.card (tupleFiber m E) = Fintype.card (Fin m ≃ T) :=
      Fintype.card_congr (tupleOrderEquiv m E hE)
    _ = Nat.factorial (Fintype.card (Fin m)) := Fintype.card_equiv e
    _ = Nat.factorial m := by simp

private theorem tupleEvent_card {n m : ℕ} [Fintype (Pair (Fin n))]
    (A : Finset (Sym2 (Fin n)) → Prop)
    (hm : m ≤ n.choose 2) :
    (Finset.univ.filter (fun x : EdgeTuple (Fin n) m =>
      DistinctPrefix x ∧ A (tupleSupport x))).card =
      ((simpleGraphsWithEdges (V := Fin n) m).filter A).card * Nat.factorial m := by
  letI : DecidableEq (Fin n) := Classical.decEq (Fin n)
  let graphs := simpleGraphsWithEdges (V := Fin n) m
  let tuples := Finset.univ.filter (fun x : EdgeTuple (Fin n) m =>
    DistinctPrefix x ∧ A (tupleSupport x))
  have hmaps : (tuples : Set (EdgeTuple (Fin n) m)).MapsTo tupleSupport graphs := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2.1
    have hcard : (tupleSupport x).card = m := by
      rw [tupleSupport]
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro i hi j hj hij
        apply hx'
        exact Subtype.ext hij
    have hsub : tupleSupport x ⊆ completeEdges (V := Fin n) := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨i, -, hi⟩
      rw [← hi]
      exact (pairCompleteEquiv (x i)).property
    change tupleSupport x ∈ (completeEdges (V := Fin n)).powerset.filter
      (fun E => E.card = m)
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hsub, hcard⟩
  have hfiber (E : Finset (Sym2 (Fin n))) (hE : E ∈ graphs) :
      (tuples.filter (fun x => tupleSupport x = E)).card =
        if A E then Nat.factorial m else 0 := by
    by_cases hA : A E
    · rw [if_pos hA]
      have hmem : E ∈ (completeEdges (V := Fin n)).powerset.filter
          (fun E => E.card = m) := by
        change E ∈ (completeEdges (V := Fin n)).powerset.filter
          (fun E => E.card = m) at hE
        exact hE
      have hE' : E ⊆ completeEdges (V := Fin n) :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hmem).1
      have hcardE : E.card = m := (Finset.mem_filter.mp hmem).2
      have heq : tuples.filter (fun x => tupleSupport x = E) =
          Finset.univ.filter (fun x : EdgeTuple (Fin n) m =>
            DistinctPrefix x ∧ tupleSupport x = E) := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_filter.mp hx with ⟨hxT, hxeq⟩
          rcases Finset.mem_filter.mp hxT with ⟨_, hxDA⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            ⟨hxDA.1, hxeq⟩⟩
        · intro hx
          rcases Finset.mem_filter.mp hx with ⟨_, ⟨hd, hxeq⟩⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hxeq⟩
          refine ⟨hd, ?_⟩
          rw [hxeq]
          exact hA
      rw [heq]
      have hcardFiber :
          (Finset.univ.filter (fun x : EdgeTuple (Fin n) m =>
            DistinctPrefix x ∧ tupleSupport x = E)).card =
            Fintype.card (tupleFiber m E) := by
        simpa [tupleFiber] using
          (Fintype.card_subtype (fun x : EdgeTuple (Fin n) m =>
            DistinctPrefix x ∧ tupleSupport x = E)).symm
      rw [hcardFiber]
      exact tupleFiber_card m E hE' hcardE
    · rw [if_neg hA]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx
      intro hxeq
      have hxA := (Finset.mem_filter.mp hx).2.2
      apply hA
      rw [← hxeq]
      exact hxA
  calc
    tuples.card = ∑ E ∈ graphs, (tuples.filter (fun x => tupleSupport x = E)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ E ∈ graphs, (if A E then Nat.factorial m else 0) := by
      apply Finset.sum_congr rfl
      intro E hE
      exact hfiber E hE
    _ = (graphs.filter A).card * Nat.factorial m := by
      rw [← Finset.sum_filter]
      exact Finset.sum_const_nat (fun _ _ => rfl)

private theorem uniformProb_card {α : Type*} [Fintype α] (P : α → Prop) :
    uniformProb P = ( (Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := by
  classical
  unfold uniformProb uniformMean
  simp only [indicator]
  change (∑ a ∈ (Finset.univ : Finset α), if P a then (1 : ℝ) else 0) /
      (Fintype.card α : ℝ) = _
  rw [Finset.sum_boole]

theorem SA_X50aStatement_holds : ThLean.BP.SA.SA_X50aStatement := by
  classical
  intro n m hn hm A
  letI : DecidablePred (fun x : EdgeTuple (Fin n) m =>
      DistinctPrefix x ∧ A (edgeSupport (tupleGraph x))) :=
    fun x => Classical.propDecidable _
  letI : DecidablePred (fun x : EdgeTuple (Fin n) m => DistinctPrefix x) :=
    fun x => Classical.propDecidable _
  let graphs := simpleGraphsWithEdges (V := Fin n) m
  let gCount := graphs.card
  let aCount := (graphs.filter A).card
  let tupleCount := Fintype.card (EdgeTuple (Fin n) m)
  have hpair := ThLean.W.BR01.PairBridgeStatement_holds n
  have hPairCard : Fintype.card (Pair (Fin n)) = n.choose 2 := hpair.2.1
  have hCompleteCard : (completeEdges (V := Fin n)).card = n.choose 2 := by
    calc
      (completeEdges (V := Fin n)).card =
          Fintype.card {e : Sym2 (Fin n) // e ∈ completeEdges (V := Fin n)} :=
        (Fintype.card_coe (completeEdges (V := Fin n))).symm
      _ = Fintype.card (Pair (Fin n)) := Fintype.card_congr pairCompleteEquiv.symm
      _ = n.choose 2 := hPairCard
  have hPairPos : 0 < Fintype.card (Pair (Fin n)) := by
    rw [hPairCard]
    exact Nat.choose_pos (by omega)
  have hTuplePos : 0 < tupleCount := by
    have htc : tupleCount = Fintype.card (Pair (Fin n)) ^ m := by
      simp [tupleCount, EdgeTuple]
    rw [htc]
    exact Nat.pow_pos hPairPos
  have hGraphCount : gCount = (n.choose 2).choose m := by
    dsimp [gCount, graphs, simpleGraphsWithEdges]
    rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard, hCompleteCard]
  have hGraphPos : 0 < gCount := by
    rw [hGraphCount]
    exact Nat.choose_pos hm
  have hEventCount :
      (Finset.univ.filter (fun x : EdgeTuple (Fin n) m =>
        DistinctPrefix x ∧ A (edgeSupport (tupleGraph x)))).card =
          aCount * Nat.factorial m := by
    simpa [aCount, graphs, tupleSupport_eq_edgeSupport] using tupleEvent_card (n := n) (m := m) A hm
  have hDistinctCount :
      (Finset.univ.filter (fun x : EdgeTuple (Fin n) m => DistinctPrefix x)).card =
        gCount * Nat.factorial m := by
    simpa [gCount, graphs] using tupleEvent_card (n := n) (m := m) (fun _ => True) hm
  have hTupleCast : (tupleCount : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hTuplePos)
  have hGraphCast : (gCount : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hGraphPos)
  have hJointProb :
      uniformProb (fun x : EdgeTuple (Fin n) m =>
        DistinctPrefix x ∧ A (edgeSupport (tupleGraph x))) =
        ((aCount * Nat.factorial m : ℕ) : ℝ) / (tupleCount : ℝ) := by
    unfold uniformProb uniformMean
    simp only [indicator]
    change (∑ x ∈ (Finset.univ : Finset (EdgeTuple (Fin n) m)),
      if DistinctPrefix x ∧ A (edgeSupport (tupleGraph x)) then (1 : ℝ) else 0) /
      (Fintype.card (EdgeTuple (Fin n) m) : ℝ) = _
    rw [Finset.sum_boole, hEventCount]
  have hDistinctProb : distinctProbability n m =
      ((gCount * Nat.factorial m : ℕ) : ℝ) / (tupleCount : ℝ) := by
    unfold distinctProbability uniformProb uniformMean
    simp only [indicator]
    change (∑ x ∈ (Finset.univ : Finset (EdgeTuple (Fin n) m)),
      if DistinctPrefix x then (1 : ℝ) else 0) /
      (Fintype.card (EdgeTuple (Fin n) m) : ℝ) = _
    rw [Finset.sum_boole, hDistinctCount]
  have hSimple : simpleEvent n m A = (aCount : ℝ) / (gCount : ℝ) := rfl
  calc
    uniformProb (fun x : EdgeTuple (Fin n) m =>
        DistinctPrefix x ∧ A (edgeSupport (tupleGraph x))) =
      ((aCount * Nat.factorial m : ℕ) : ℝ) / (tupleCount : ℝ) := hJointProb
    _ = distinctProbability n m * simpleEvent n m A := by
      rw [hDistinctProb, hSimple]
      push_cast
      field_simp [hGraphCast, hTupleCast]
      <;> ring

example : ThLean.BP.SA.SA_X50aStatement := SA_X50aStatement_holds

end ThLean.W.SA65

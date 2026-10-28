import ThLean.W.S512.Multinomial

noncomputable section
open scoped BigOperators Topology
open ThresholdFoundations

namespace ThLean.W.S512

private abbrev blockFiber {I J : Type*} [DecidableEq J] (p : I → J) (j : J) :=
  {i : I // p i = j}

@[instance_reducible]
private noncomputable instance blockFiberFintype {I J : Type*} [Fintype I]
    [DecidableEq J] (p : I → J) (j : J) : Fintype (blockFiber p j) := by
  classical
  refine Fintype.ofFinset (p := {i : I | p i = j})
    (Finset.univ.filter (fun i : I => p i = j)) ?_
  intro i
  simp

private abbrev blockConstraint {I J : Type*} [Fintype I] [DecidableEq J] (p : I → J)
    (c : J → ℕ) (x : I → ℕ) : Prop :=
  ∀ j, ∑ i ∈ Finset.univ.filter (fun i : I => p i = j), x i = c j

private abbrev blockGood {I J : Type*} [Fintype I] [DecidableEq J]
    (p : I → J) (c : J → ℕ) :=
  {x : I → ℕ // blockConstraint p c x}

private abbrev blockFun {I J : Type*} [DecidableEq J] (p : I → J) :=
  (j : J) → blockFiber p j → ℕ

private noncomputable def blockSets {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (p : I → J) (c : J → ℕ) : Finset (blockFun p) := by
  classical
  exact Fintype.piFinset (fun j => Finset.piAntidiag Finset.univ (c j))

private abbrev blockHist {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (p : I → J) (c : J → ℕ) :=
  {x : blockFun p // x ∈ blockSets p c}

private noncomputable def blockAssignmentEquiv {I J : Type*} [DecidableEq J]
    (p : I → J) : (I → ℕ) ≃ blockFun p :=
  (Equiv.piCongrSigmaFiber (f := p) (fun _ => Equiv.refl ℕ)).symm.trans
    (Equiv.piCurry (fun _ _ => ℕ))

@[simp]
private theorem blockAssignmentEquiv_apply {I J : Type*} [DecidableEq J]
    (p : I → J) (x : I → ℕ) (j : J) (i : blockFiber p j) :
    blockAssignmentEquiv p x j i = x i.1 := by
  change ((Equiv.piCongrSigmaFiber (f := p) (fun _ => Equiv.refl ℕ)).symm x)
    ⟨j, i⟩ = x i.1
  simp

private theorem blockAssignment_sum_eq_filter {I J : Type*} [Fintype I]
    [DecidableEq J] (p : I → J) (x : I → ℕ) (j : J) :
    (∑ i : blockFiber p j, blockAssignmentEquiv p x j i) =
      ∑ i ∈ Finset.univ.filter (fun i : I => p i = j), x i := by
  classical
  calc
    (∑ i : blockFiber p j, blockAssignmentEquiv p x j i) =
        ∑ i : blockFiber p j, x i.1 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact blockAssignmentEquiv_apply p x j i
    _ = ∑ i ∈ Finset.univ.filter (fun i : I => p i = j), x i :=
      (Finset.sum_subtype
        (s := Finset.univ.filter (fun i : I => p i = j))
        (p := fun i : I => p i = j)
        (by intro i; simp [blockFiber]) x).symm

private theorem blockConstraint_iff_hist {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (p : I → J) (c : J → ℕ) (x : I → ℕ) :
    blockConstraint p c x ↔ blockAssignmentEquiv p x ∈ blockSets p c := by
  classical
  change blockConstraint p c x ↔
    blockAssignmentEquiv p x ∈ Fintype.piFinset
      (fun j => Finset.piAntidiag Finset.univ (c j))
  rw [Fintype.mem_piFinset]
  constructor
  · intro hx j
    apply Finset.mem_piAntidiag.mpr
    constructor
    · rw [blockAssignment_sum_eq_filter]
      exact hx j
    · intro i hi
      exact Finset.mem_univ _
  · intro hx j
    have h := (Finset.mem_piAntidiag.mp (hx j)).1
    calc
      (∑ i ∈ Finset.univ.filter (fun i : I => p i = j), x i) =
          ∑ i : blockFiber p j, blockAssignmentEquiv p x j i :=
        (blockAssignment_sum_eq_filter p x j).symm
      _ = c j := by simpa using h

private noncomputable def blockHistFintype {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (p : I → J) (c : J → ℕ) : Fintype (blockHist p c) := by
  classical
  exact Fintype.ofFinset (blockSets p c) (fun _ => Iff.rfl)

private noncomputable def blockEquiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (p : I → J) (c : J → ℕ) : blockGood p c ≃ blockHist p c :=
  (blockAssignmentEquiv p).subtypeEquiv (blockConstraint_iff_hist p c)

private theorem blockGood_mass_sum {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (r : I → ℝ) (p : I → J) (c : J → ℕ)
    [Fintype (blockGood p c)] :
    (∑ x : blockGood p c, ∏ i, poissonWeight (r i) (x.1 i)) =
      ∏ j, poissonWeight
        (∑ i ∈ Finset.univ.filter (fun i : I => p i = j), r i) (c j) := by
  classical
  let t : (j : J) → Finset (blockFiber p j → ℕ) :=
    fun j => Finset.piAntidiag Finset.univ (c j)
  letI : Fintype (blockHist p c) := blockHistFintype p c
  have hsplit (x : I → ℕ) :
      (∏ i, poissonWeight (r i) (x i)) =
        ∏ j, ∏ i : blockFiber p j, poissonWeight (r i.1) (x i.1) := by
    symm
    exact Fintype.prod_fiberwise p (fun i => poissonWeight (r i) (x i))
  calc
    (∑ x : blockGood p c, ∏ i, poissonWeight (r i) (x.1 i)) =
        ∑ y : blockHist p c, ∏ j, ∏ i : blockFiber p j,
          poissonWeight (r i.1) (y.1 j i) := by
      apply Fintype.sum_equiv (blockEquiv p c)
      intro x
      exact hsplit x.1
    _ = ∑ y ∈ blockSets p c, ∏ j, ∏ i : blockFiber p j,
          poissonWeight (r i.1) (y j i) := by
      exact Finset.sum_coe_sort (blockSets p c)
        (fun y => ∏ j, ∏ i : blockFiber p j, poissonWeight (r i.1) (y j i))
    _ = ∏ j, ∑ z ∈ t j, ∏ i : blockFiber p j,
          poissonWeight (r i.1) (z i) := by
      change (∑ y ∈ Fintype.piFinset t,
        ∏ j, ∏ i : blockFiber p j, poissonWeight (r i.1) (y j i)) = _
      rw [← Finset.prod_univ_sum t
        (fun j z => ∏ i : blockFiber p j, poissonWeight (r i.1) (z i))]
    _ = ∏ j, poissonWeight
          (∑ i ∈ Finset.univ.filter (fun i : I => p i = j), r i) (c j) := by
      apply Finset.prod_congr rfl
      intro j hj
      calc
        (∑ z ∈ t j, ∏ i : blockFiber p j, poissonWeight (r i.1) (z i)) =
            poissonWeight (∑ i : blockFiber p j, r i.1) (c j) :=
          poissonWeight_piAntidiag (fun i : blockFiber p j => r i.1) (c j)
        _ = poissonWeight
            (∑ i ∈ Finset.univ.filter (fun i : I => p i = j), r i) (c j) := by
          congr 1
          exact (Finset.sum_subtype
            (Finset.univ.filter (fun i : I => p i = j))
            (by intro i; simp [blockFiber]) r).symm

theorem S5_E06BStatement_holds : ThLean.BP.S5.S5_E06BStatement := by
  classical
  intro I J _ _ r hr p c
  letI : Fintype (blockHist p c) := blockHistFintype p c
  letI : Fintype (blockGood p c) :=
    Fintype.ofEquiv (blockHist p c) (blockEquiv p c).symm
  let S : Finset (I → ℕ) :=
    (Finset.univ : Finset (blockGood p c)).map
      ⟨Subtype.val, Subtype.val_injective⟩
  have hsupp : ∀ x, x ∉ S →
      (if blockConstraint p c x then ∏ i, poissonWeight (r i) (x i) else 0) = 0 := by
    intro x hx
    by_cases h : blockConstraint p c x
    · have hxS : x ∈ S := by
        simp only [S, Finset.mem_map]
        exact ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩
      exact (hx hxS).elim
    · simp [h]
  have hhas := hasSum_sum_of_ne_finset_zero
    (L := SummationFilter.unconditional (I → ℕ)) hsupp
  have hsum : (∑ x ∈ S,
      if blockConstraint p c x then ∏ i, poissonWeight (r i) (x i) else 0) =
      ∏ j, poissonWeight
        (∑ i ∈ Finset.univ.filter (fun i : I => p i = j), r i) (c j) := by
    calc
      _ = ∑ x : blockGood p c, ∏ i, poissonWeight (r i) (x.1 i) := by
        simp only [S, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro x hx
        simp [blockConstraint, x.property]
      _ = _ := blockGood_mass_sum r p c
  rw [← hsum]
  simpa only [blockConstraint] using hhas

end ThLean.W.S512

import ThLean.BP.S3.Poisson

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S343

open ThresholdFoundations
open ThLean.BP.S3

universe u

theorem S3_38bStatement_of_deps
    (h03 : ThLean.BP.S3.S3_03aStatement.{u})
    (h37a : ThLean.BP.S3.S3_37aStatement.{u})
    (h37b : ThLean.BP.S3.S3_37bStatement.{u}) :
    ThLean.BP.S3.S3_38bStatement.{u} := by
  classical
  intro V instV hV a t ht Starget B ys
  let S : Finset V := Finset.univ.erase a
  have h03V := h03 V (by omega : 2 ≤ Fintype.card V)
  have hpair : Fintype.card (Pair V) = (Fintype.card V).choose 2 := h03V.1
  have hScard : S.card = Fintype.card V - 1 := by
    simp [S]
  have hSge : 2 ≤ S.card := by omega
  have hS0 : ({a} : Finset V).card ≤ 1 := by simp
  let ys' : {v : V // v ∈ ({a} : Finset V)} → List V := fun _ => ys
  have hloop (w : List (Pair V)) : Loopless (listGraph w) := by
    intro v
    change ((w.filter (fun e : Pair V => e.val = s(v, v))).length) = 0
    rw [List.length_eq_zero_iff]
    apply List.filter_eq_nil_iff.mpr
    intro e he h
    exact e.property v (of_decide_eq_true h)
  have hzero (w : List (Pair V)) :
      inducedGraph (listGraph w) ({a} : Finset V) =
        (0 : MGraph {v : V // v ∈ ({a} : Finset V)}) :=
    (h37b V ({a} : Finset V) hS0).1 (listGraph w) (hloop w)
  have hSdiff : ((Finset.univ : Finset V) \ ({a} : Finset V)).card = S.card := by
    rw [Finset.sdiff_singleton_eq_erase]
  have hSdiffge : 2 ≤ ((Finset.univ : Finset V) \ ({a} : Finset V)).card := by
    rw [hSdiff]
    exact hSge
  have hSet : ((Finset.univ : Finset V) \ ({a} : Finset V)) = S := by
    rw [Finset.sdiff_singleton_eq_erase]
  have hsplitAll := h37a V ({a} : Finset V) hV hSdiffge
  rw [hSet] at hsplitAll
  have hsplit := hsplitAll t ht B
    (0 : MGraph {v : V // v ∈ ({a} : Finset V)}) ys'
  have hevent :
      (fun w : List (Pair V) =>
        inducedGraph (listGraph w) Starget = B ∧ neighborList a Starget w = ys) =
      (fun w : List (Pair V) =>
        inducedGraph (listGraph w) Starget = B ∧
        inducedGraph (listGraph w) ({a} : Finset V) = 0 ∧
        ∀ x : {v : V // v ∈ ({a} : Finset V)},
          neighborList x.val Starget w = ys' x) := by
    funext w
    apply propext
    constructor
    · rintro ⟨hB, hys⟩
      refine ⟨?_, hzero w, ?_⟩
      · exact hB
      · intro x
        have hx : x.val = a := Finset.mem_singleton.mp x.property
        simpa [hx] using hys
    · rintro ⟨hB, _, hys⟩
      refine ⟨?_, ?_⟩
      · exact hB
      · have ha : (⟨a, Finset.mem_singleton_self a⟩ :
          {v : V // v ∈ ({a} : Finset V)}).val = a := rfl
        simpa [ha] using hys ⟨a, Finset.mem_singleton_self a⟩
  have hprob := congrArg (poissonWordProb t) hevent
  rw [← hprob] at hsplit
  have hN : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hN0 : (Fintype.card V : ℝ) ≠ 0 := by positivity
  have hN1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by linarith
  have hN2 : (Fintype.card V : ℝ) - 2 ≠ 0 := by linarith
  have hpaircast : (Fintype.card (Pair V) : ℝ) =
      ((Fintype.card V).choose 2 : ℝ) := by exact_mod_cast hpair
  have hrateGraph :
      t * ((S.card.choose 2 : ℕ) : ℝ) / (Fintype.card (Pair V) : ℝ) =
        ((Fintype.card V : ℝ) - 2) * t / (Fintype.card V : ℝ) := by
    rw [hpaircast, hScard, Nat.cast_choose_two, Nat.cast_choose_two]
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
    push_cast
    field_simp
    ring
  have hrateList :
      t * (S.card : ℝ) / (Fintype.card (Pair V) : ℝ) =
        2 * t / (Fintype.card V : ℝ) := by
    rw [hpaircast, hScard, Nat.cast_choose_two]
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
    push_cast
    field_simp
  have hnu :
      (fun v : V => if v ∈ S then 1 / (S.card : ℝ) else 0) =
      (fun v : V => if v ≠ a then 1 / ((Fintype.card V : ℝ) - 1) else 0) := by
    funext v
    by_cases hv : v = a <;> simp [S, hv, hScard, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
  have hzeroMean :
      poissonGraphMean (V := {v : V // v ∈ ({a} : Finset V)}) 0
        (fun G => indicator (G = 0)) = 1 := by
    simpa [indicator] using
      (h37b V ({a} : Finset V) hS0).2 (0 : MGraph {v : V // v ∈ ({a} : Finset V)})
  have hrootRate :
      t * ((({a} : Finset V).card.choose 2 : ℕ) : ℝ) /
          (Fintype.card (Pair V) : ℝ) = 0 := by
    simp
  letI : Unique {v : V // v ∈ ({a} : Finset V)} :=
    ⟨⟨a, Finset.mem_singleton_self a⟩, fun x => by
      apply Subtype.ext
      exact Finset.mem_singleton.mp x.property⟩
  have hprod :
      (∏ x : {v : V // v ∈ ({a} : Finset V)},
        poissonListMass (t * (S.card : ℝ) / (Fintype.card (Pair V) : ℝ))
          (fun v : V => if v ∈ S then 1 / (S.card : ℝ) else 0) (ys' x)) =
      poissonListMass (2 * t / (Fintype.card V : ℝ))
        (fun v : V => if v ≠ a then 1 / ((Fintype.card V : ℝ) - 1) else 0) ys := by
    rw [Fintype.prod_unique]
    simp only [ys', hrateList, hnu]
  rw [hrateGraph, hrootRate, hzeroMean, hprod] at hsplit
  simpa [S] using hsplit

end ThLean.W.S343

import ThLean.BP.S5.Identification

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S519
open ThresholdFoundations
open ThLean.BP.S5

set_option maxHeartbeats 2000000

private theorem uniformProb_nonneg {A : Type} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProb P := by
  unfold uniformProb uniformMean indicator
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro a ha
    split <;> norm_num
  · positivity

private theorem uniformMean_fintype_irrel {A : Type} (i j : Fintype A)
    (f : A → ℝ) : @uniformMean A i f = @uniformMean A j f := by
  have h : i = j := Subsingleton.elim _ _
  cases h
  rfl

/-- The real occupation identity follows from the summable identification
failure sequence and the scale-one real Poisson occupation theorem. -/
theorem S5_17CStatement_of_deps
    (h17B : S5_17BStatement) (h10 : S5_10Statement) :
    S5_17CStatement := by
  intro q N D hq hN hD hDN
  let a : ℕ → ℝ := fun m =>
    uniformMean (fun x : EdgeTuple (Fin N) m =>
      identificationFailureProbability q D (tupleGraph x))
  have hprob (m : ℕ) (x : EdgeTuple (Fin N) m) :
      0 ≤ identificationFailureProbability q D (tupleGraph x) := by
    unfold identificationFailureProbability
    exact uniformProb_nonneg _
  have ha_nonneg : ∀ m, 0 ≤ a m := by
    intro m
    unfold a uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x hx
      exact hprob m x
    · positivity
  have hHas : HasSum a (advanceReal q N D) := by
    simpa [a] using (h17B q N D hq hN hD hDN).2.2.2.2
  have hsum : (∑' m, a m) = advanceReal q N D := hHas.tsum_eq
  have hocc := (h10 1 (by norm_num)).2 a ha_nonneg hHas.summable
  have hfun (s : ℝ) : discrepancy q N D s = poissonMixture s a := by
    unfold discrepancy poissonGraphMean
    congr 1
    funext m
    unfold a
    exact uniformMean_fintype_irrel _ _ _
  have hfun' : discrepancy q N D = fun s : ℝ => poissonMixture s a := by
    funext s
    exact hfun s
  refine ⟨?_, ?_⟩
  · rw [hfun']
    simpa only [one_mul] using hocc.1
  · have hEq := hocc.2
    rw [hsum] at hEq
    rw [hfun']
    simpa using hEq

end ThLean.W.S519

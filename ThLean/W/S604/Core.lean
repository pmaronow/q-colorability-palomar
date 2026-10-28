import ThLean.BP.S6.Measure

noncomputable section
open scoped BigOperators
open MeasureTheory ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S604

theorem S6_02bStatement_holds : ThLean.BP.S6.S6_02bStatement := by
  classical
  intro A Ω _ _ _ _ μ _ X hX hmass
  have hmean : ∀ F : A → ℝ,
      Measurable (F ∘ X) ∧ Integrable (F ∘ X) μ ∧
        (∫ ω, F (X ω) ∂μ) = uniformMean F := by
    intro F
    have hmeasF : Measurable F := measurable_of_finite F
    have hmeas : Measurable (F ∘ X) := hmeasF.comp hX
    have hbound : ∀ ω, ‖F (X ω)‖ ≤ ∑ a : A, ‖F a‖ := by
      intro ω
      exact Finset.single_le_sum (fun a ha => norm_nonneg (F a)) (Finset.mem_univ (X ω))
    have hint : Integrable (F ∘ X) μ :=
      Integrable.of_bound hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hbound)
    refine ⟨hmeas, hint, ?_⟩
    have hfiber (a : A) : MeasurableSet {ω | X ω = a} :=
      measurableSet_preimage hX (measurableSet_singleton a)
    have hterm (a : A) : Integrable (fun ω => ({ω | X ω = a}.indicator (fun _ => F a)) ω) μ :=
      (integrable_const (F a)).integrableOn.integrable_indicator (hfiber a)
    have hdecomp' : (fun ω => F (X ω)) =
        fun ω => ∑ a : A, ({ω | X ω = a}.indicator (fun _ => F a)) ω := by
      funext ω
      simp [Set.indicator]
    calc
      (∫ ω, F (X ω) ∂μ) = ∫ ω, ∑ a : A, ({ω | X ω = a}.indicator (fun _ => F a)) ω ∂μ := by
        rw [hdecomp']
      _ = ∑ a : A, ∫ ω, ({ω | X ω = a}.indicator (fun _ => F a)) ω ∂μ := by
        simpa using (integral_finsetSum (μ := μ) Finset.univ (fun a ha => hterm a))
      _ = ∑ a : A, (1 / (Fintype.card A : ℝ)) * F a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [integral_indicator_const (F a) (hfiber a), smul_eq_mul, hmass a]
      _ = uniformMean F := by
        rw [uniformMean]
        rw [← Finset.mul_sum]
        ring
  refine ⟨hmean, ?_⟩
  intro P
  let B : Set A := {a | P a}
  have hB : MeasurableSet B := by
    apply Set.Finite.measurableSet
    exact Set.finite_univ.subset (Set.subset_univ B)
  have hs : MeasurableSet {ω | P (X ω)} := measurableSet_preimage hX hB
  have hfun : (fun ω => indicator (P (X ω))) =
      {ω | P (X ω)}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp [ThresholdFoundations.indicator, Set.indicator]
  have hInt := (hmean (fun a => indicator (P a))).2.2
  have hInt' : (∫ ω, {ω | P (X ω)}.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      uniformMean (fun a => indicator (P a)) := by
    rw [← hfun]
    exact hInt
  refine ⟨hs, ?_⟩
  calc
    μ.real {ω | P (X ω)} = ∫ ω, {ω | P (X ω)}.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      (integral_indicator_one hs).symm
    _ = uniformProb P := by simpa [uniformProb] using hInt'

end ThLean.W.S604

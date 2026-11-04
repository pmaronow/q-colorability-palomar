module

public import ThLean.BP.S5.Identification

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators Topology

namespace ThLean.W.S523S
open ThresholdFoundations ThLean.BP.S5

theorem poissonGraphMean_measurable {V : Type} [Fintype V]
    (f : MGraph V → ℝ) : Measurable (fun s : ℝ => poissonGraphMean s f) := by
  classical
  apply Measurable.tsum
  intro m
  exact (by fun_prop [poissonWeight] :
    Continuous (fun s : ℝ => poissonWeight s m *
      uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)))).measurable

theorem addedFailure_measurable {V : Type} [Fintype V]
    (q : ℕ) (a b : ℝ) :
    Measurable (fun s : ℝ => addedFailure (V := V) q (a * s) (b * s)) := by
  classical
  unfold addedFailure poissonMixture
  apply Measurable.tsum
  intro j
  apply Measurable.mul
  · exact (by fun_prop [poissonWeight] :
      Continuous (fun s : ℝ => poissonWeight (b * s) j)).measurable
  · unfold blockingMean countMean independentPoissonGraphMean
    apply Measurable.tsum
    intro G
    apply Measurable.mul
    · unfold independentPoissonGraphMass
      apply Finset.measurable_prod
      intro e _
      unfold perPairRate
      split_ifs <;> exact (by fun_prop [poissonWeight] :
        Continuous _).measurable
    · exact measurable_const

theorem fixedIdentification_measurable (q N : ℕ) (Z : Finset (Fin N)) :
    Measurable (fun s : Set.Ici (0 : ℝ) =>
      poissonGraphMean s.val (fun G : MGraph (Fin N) =>
        indicator (Colorable q G ∧ ¬ Colorable q (identify G Z)))) ∧
    Measurable (fun s : Set.Ici (0 : ℝ) =>
      addedFailure (V := {v : Fin N // v ∉ Z}) q
        (lowEdgeRate N * s.val) (Z.card * neighborMean N Z.card s.val)) := by
  constructor
  · exact (poissonGraphMean_measurable (fun G : MGraph (Fin N) =>
      indicator (Colorable q G ∧ ¬ Colorable q (identify G Z)))).comp
      measurable_subtype_coe
  · convert (addedFailure_measurable (V := {v : Fin N // v ∉ Z}) q
        (lowEdgeRate N) (Z.card * lowEdgeRate N * (N - Z.card : ℕ))).comp
        measurable_subtype_coe using 1
    funext s
    congr 1
    unfold neighborMean
    ring

end ThLean.W.S523S

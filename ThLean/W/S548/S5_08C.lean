import ThLean.BP.S5.Poisson

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal

namespace ThLean.W.S548

theorem S5_08CStatement_holds : ThLean.BP.S5.S5_08CStatement := by
  classical
  intro I instI r hr f hf
  have hcoord (x : I → ℕ) :
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        ∏ i, ThresholdFoundations.poissonWeight (r i * t.val) (x i)) := by
    have hterm (i : I) :
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          ThresholdFoundations.poissonWeight (r i * t.val) (x i)) := by
      fun_prop [ThresholdFoundations.poissonWeight]
    convert continuous_finsetProd Finset.univ (fun i hi => hterm i) using 1
  have hmeas (x : I → ℕ) :
      Measurable (fun t : Set.Ici (0 : ℝ) =>
        (∏ i, ThresholdFoundations.poissonWeight (r i * t.val) (x i)) * f x) := by
    exact ((hcoord x).mul continuous_const).measurable
  exact Measurable.tsum hmeas

end ThLean.W.S548

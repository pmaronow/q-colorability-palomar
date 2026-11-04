module

public import ThLean.BP.S3.Tails

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S355

open ThresholdFoundations ThLean.BP.S3

private theorem poissonEvent_eq_measure (z : ℝ) (hz : 0 < z) (P : ℕ → Prop)
    (hP : MeasurableSet {n | P n}) :
    poissonEvent z P =
      (ProbabilityTheory.poissonMeasure (⟨z, le_of_lt hz⟩ : NNReal)).real {n | P n} := by
  let r : NNReal := ⟨z, le_of_lt hz⟩
  unfold poissonEvent
  have hterms : ∀ n : ℕ,
      (if P n then ENNReal.ofReal (poissonWeight z n) else 0) =
        Set.indicator {n | P n} (fun n => ProbabilityTheory.poissonMeasure r {n}) n := by
    intro n
    by_cases hp : P n
    · simp only [if_pos hp]
      rw [Set.indicator_of_mem (show n ∈ {n | P n} from hp)]
      rw [ProbabilityTheory.poissonMeasure_singleton]
      congr 1
    · simp [hp]
  calc
    (∑' n : ℕ, if P n then ENNReal.ofReal (poissonWeight z n) else 0).toReal =
        (∑' n : ℕ, Set.indicator {n | P n}
          (fun n => ProbabilityTheory.poissonMeasure r {n}) n).toReal := by
            congr 1
            exact tsum_congr hterms
    _ = (ProbabilityTheory.poissonMeasure r {n | P n}).toReal := by
      rw [MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hP]
    _ = (ProbabilityTheory.poissonMeasure r).real {n | P n} := rfl

theorem S3_48Statement_of_deps
    (h44 : S3_44Statement.{0}) (h45 : S3_45Statement) (h46 : S3_46Statement) :
    S3_48Statement := by
  intro z s hz hs
  let r : NNReal := ⟨z, le_of_lt hz⟩
  let θ : ℝ := Real.log (1 + s / z)
  let X : ℕ → ℝ := fun n => (n : ℝ)
  have hx : 0 < s / z := div_pos hs hz
  have harg : 1 < 1 + s / z := by linarith
  have hθ : 0 ≤ θ := by
    dsimp [θ]
    exact le_of_lt (Real.log_pos harg)
  have hexpθ : Real.exp θ = 1 + s / z := by
    dsimp [θ]
    exact Real.exp_log (by linarith)
  have hInt : Integrable (fun n : ℕ => Real.exp (θ * X n))
      (ProbabilityTheory.poissonMeasure r) := by
    simpa [X, mul_comm] using (h45 r θ).1
  have hSet : MeasurableSet {n : ℕ | z+s ≤ (n : ℝ)} := by
    exact Set.Countable.measurableSet (Set.to_countable _)
  have hChernoff := (h44 ℕ (ProbabilityTheory.poissonMeasure r) X (z+s) θ
    (by fun_prop) hInt).1 hθ
  have hMoment := (h45 r θ).2
  rw [hMoment] at hChernoff
  have hrval : (r : ℝ) = z := rfl
  rw [hrval] at hChernoff
  have hexp :
      Real.exp (-θ*(z+s)) * Real.exp (z*(Real.exp θ - 1)) =
        Real.exp (-z * entropy (s/z)) := by
    rw [← Real.exp_add, hexpθ]
    dsimp [θ, entropy]
    field_simp
    <;> ring
  have hEntropy := h46.1 (s/z) (le_of_lt hx)
  have hExponent :
      -z * entropy (s/z) ≤ -(s^2)/(2*(z+s)) := by
    have hmul := mul_le_mul_of_nonpos_left hEntropy (by linarith : -z ≤ 0)
    have hratio : z * ((s/z)^2 / (2*(1+s/z))) = s^2/(2*(z+s)) := by
      field_simp [ne_of_gt hz]
      <;> ring_nf
    calc
      -z * entropy (s/z) ≤ -z * ((s/z)^2 / (2*(1+s/z))) := hmul
      _ = -(s^2/(2*(z+s))) := by
        calc
          -z * ((s/z)^2 / (2*(1+s/z))) = -(z * ((s/z)^2 / (2*(1+s/z)))) := by ring
          _ = -(s^2/(2*(z+s))) := congrArg Neg.neg hratio
      _ = -(s^2)/(2*(z+s)) := by ring
  calc
    poissonEvent z (fun n => z+s ≤ (n : ℝ)) =
        (ProbabilityTheory.poissonMeasure r).real {n | z+s ≤ (n : ℝ)} :=
          poissonEvent_eq_measure z hz _ hSet
    _ ≤ Real.exp (-θ*(z+s)) * Real.exp (z*(Real.exp θ - 1)) := by
          simpa [X] using hChernoff
    _ = Real.exp (-z * entropy (s/z)) := hexp
    _ ≤ Real.exp (-(s^2)/(2*(z+s))) := Real.exp_le_exp.mpr hExponent

end ThLean.W.S355

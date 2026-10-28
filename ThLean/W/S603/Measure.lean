import ThLean.BP.S6.Measure

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations MeasureTheory ProbabilityTheory

namespace ThLean.W.S603

local instance edgeMeasurable (n : ℕ) : MeasurableSpace (ThLean.BP.S6.Edge n) := ⊤
local instance edgeSingletons (n : ℕ) : MeasurableSingletonClass (ThLean.BP.S6.Edge n) :=
  ⟨fun _ => trivial⟩

theorem S6_02aStatement_holds : ThLean.BP.S6.S6_02aStatement := by
  intro n m hn Ω _ μ _ e he x
  let hvec : Ω → (Fin m → ThLean.BP.S6.Edge n) := fun ω i => e i ω
  have hvecMeas : Measurable hvec := Measurable.of_eval fun i => he.1 i
  have hmap : μ.map hvec = Measure.pi (fun i : Fin m => μ.map (e i)) :=
    he.2.1.map_fun_eq_pi_map fun i => (he.1 i).aemeasurable
  have hmarg (i : Fin m) : (μ.map (e i)).real {x i} =
      1 / (Fintype.card (ThLean.BP.S6.Edge n) : ℝ) := by
    rw [map_measureReal_apply (he.1 i) (measurableSet_singleton (x i))]
    exact he.2.2 i (x i)
  calc
    μ.real {ω | (fun i => e i ω) = x} = (μ.map hvec).real {x} := by
      rw [map_measureReal_apply hvecMeas (measurableSet_singleton x)]
      rfl
    _ = 1 / (Fintype.card (ThLean.BP.S6.Hist n m) : ℝ) := by
      rw [hmap]
      simp only [Measure.real_def, Measure.pi_singleton, ENNReal.toReal_prod]
      simp_rw [← Measure.real_def, hmarg]
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
      simp [Finset.prod_const]

end ThLean.W.S603

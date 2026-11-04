module

public import ThLean.Defs.Extras

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ThresholdFoundations.Sanity

theorem empty_colorable {V : Type*} [Fintype V] {q : ℕ} (hq : 0 < q) :
    Colorable q (0 : MGraph V) := by
  refine ⟨fun _ => ⟨0, hq⟩, ?_⟩
  simp [IsColoring]

/-- One occurrence on each of the three sides. -/
def triangle : MGraph (Fin 3) :=
  fun e => if e = s((0 : Fin 3),1) ∨ e = s((1 : Fin 3),2) ∨ e = s((2 : Fin 3),0)
    then 1 else 0

theorem triangle_not_two_colorable : ¬ Colorable 2 triangle := by
  rintro ⟨σ, hσ⟩
  have h01 : σ 0 ≠ σ 1 := hσ 0 1 (by simp [triangle])
  have h12 : σ 1 ≠ σ 2 := hσ 1 2 (by simp [triangle])
  have h20 : σ 2 ≠ σ 0 := hσ 2 0 (by simp [triangle])
  have hn01 : (σ 0).val ≠ (σ 1).val := fun h => h01 (Fin.ext h)
  have hn12 : (σ 1).val ≠ (σ 2).val := fun h => h12 (Fin.ext h)
  have hn20 : (σ 2).val ≠ (σ 0).val := fun h => h20 (Fin.ext h)
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  have h2 := (σ 2).isLt
  omega

theorem processSurvival_zero {V : Type*} [Fintype V] {q : ℕ} (hq : 0 < q) :
    processSurvival (V := V) q 0 = 1 := by
  have hg (x : EdgeTuple V 0) : tupleGraph x = 0 := by
    ext e
    simp [tupleGraph]
  have hc (x : EdgeTuple V 0) : Colorable q (tupleGraph x) := by
    simpa [hg x] using (empty_colorable (V := V) hq)
  simp [processSurvival, survival, uniformProb, uniformMean, indicator, hc, EdgeTuple]

theorem loop_not_colorable {V : Type*} [Fintype V] (q : ℕ)
    (G : MGraph V) (a : V) (h : 0 < G s(a,a)) : ¬ Colorable q G := by
  rintro ⟨σ, hσ⟩
  exact hσ a a h rfl

theorem no_failure_is_infinity : firstFailure (fun _ => False) = ⊤ := by
  simp [firstFailure]

theorem poisson_zero : poissonWeight 0 0 = 1 := by
  simp [poissonWeight]

example : Colorable 3 (0 : MGraph (Fin 0)) := empty_colorable (by omega)
example : ¬ Colorable 2 triangle := triangle_not_two_colorable
example : processSurvival (V := Fin 1) 1 0 = 1 := processSurvival_zero (by omega)
example : firstFailure (fun _ => False) = ⊤ := no_failure_is_infinity
end ThresholdFoundations.Sanity

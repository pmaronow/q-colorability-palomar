import ThLean.BP.SA.Interpolation
import ThLean.Contrib.SA28.Endpoints

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA28
open ThresholdFoundations

/-- In the one-vertex model, every positive-length sample contains a loop. -/
theorem rho_one_vertex (q : ℕ) (c : ℝ) (hq : 1 ≤ q) :
    rho q 1 c = Real.exp (-c) := by
  have hcolor (m : ℕ) (x : Fin m → Fin 1 × Fin 1) :
      Colorable q (orderedTupleGraph x) ↔ m = 0 := by
    constructor
    · intro hc
      by_contra hm
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let i : Fin m := ⟨0, hmpos⟩
      rcases hc with ⟨σ, hσ⟩
      have hx : x i = ((0 : Fin 1), (0 : Fin 1)) := Subsingleton.elim _ _
      have hloop : 0 < orderedTupleGraph x (s((0 : Fin 1), (0 : Fin 1))) := by
        dsimp [orderedTupleGraph]
        apply Finset.card_pos.mpr
        exact ⟨i, by simp [hx]⟩
      exact hσ 0 0 hloop rfl
    · intro hm
      subst m
      have hx : orderedTupleGraph x = 0 := by
        ext e
        simp [orderedTupleGraph]
      rw [hx]
      exact ThresholdFoundations.Sanity.empty_colorable (by omega)
  have hmean (m : ℕ) :
      uniformProb (fun x : Fin m → Fin 1 × Fin 1 =>
        Colorable q (orderedTupleGraph x)) = if m = 0 then 1 else 0 := by
    simp [uniformProb, uniformMean, indicator, hcolor]
  unfold rho poissonMixture
  simp_rw [hmean, Nat.cast_one, mul_one]
  rw [tsum_eq_single 0]
  · simp [poissonWeight]
  · intro m hm
    simp [hm]

/-- At zero rate, the Poisson sample has length zero and the empty graph is colorable. -/
theorem rho_zero_rate (q n : ℕ) (hq : 1 ≤ q) (_hn : 1 ≤ n) :
    rho q n 0 = 1 := by
  have hzero (x : Fin 0 → Fin n × Fin n) :
      Colorable q (orderedTupleGraph x) := by
    have hx : orderedTupleGraph x = 0 := by
      ext e
      simp [orderedTupleGraph]
    rw [hx]
    exact ThresholdFoundations.Sanity.empty_colorable (by omega)
  have hmean :
      uniformProb (fun x : Fin 0 → Fin n × Fin n =>
        Colorable q (orderedTupleGraph x)) = 1 := by
    simp [uniformProb, uniformMean, indicator, hzero]
  unfold rho poissonMixture
  simp_rw [show (0 : ℝ) * (n : ℝ) = 0 by ring]
  rw [tsum_eq_single 0]
  · simp [poissonWeight, hmean]
  · intro m hm
    simp [poissonWeight, hm]

/-- SA_I13b from the interpolation endpoint identities `SA_I13bEndpointsStatement`;
the zero-rate and one-vertex laws are proved here. -/
theorem SA_I13bStatement_of_endpoints
    (hendpoints : ThLean.Contrib.SA28.SA_I13bEndpointsStatement) :
    ThLean.BP.SA.SA_I13bStatement := by
  refine ⟨hendpoints, ?_, ?_⟩
  · intro q n hq hn
    exact rho_zero_rate q n hq hn
  · intro q hq c hc
    exact rho_one_vertex q c hq

end ThLean.W.SA28

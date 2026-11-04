module

public import ThLean.BP.S4.Reduction

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S439

open ThresholdFoundations
open ThLean.BP.S4

private theorem uniformMean_const_mul {A : Type} [Fintype A]
    (c : ℝ) (f : A → ℝ) :
    uniformMean (fun x => c * f x) = c * uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

private theorem terminalReal_const_mul {V : Type} [Fintype V]
    (q L U : ℕ) (c : ℝ) (F : ℕ → MGraph V → Pair V → ℝ) :
    terminalReal q L U (fun h G e => c * F h G e) =
      c * terminalReal q L U F := by
  unfold terminalReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hinner (x : EdgeTuple V k) :
      uniformMean (fun e : Pair V =>
        if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
        then c * F (k + 1) (tupleGraph x) e else 0) =
      c * uniformMean (fun e : Pair V =>
        if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
        then F (k + 1) (tupleGraph x) e else 0) := by
    have hfun :
        (fun e : Pair V =>
          if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
          then c * F (k + 1) (tupleGraph x) e else 0) =
        (fun e : Pair V => c *
          (if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
           then F (k + 1) (tupleGraph x) e else 0)) := by
      funext e
      by_cases h : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e) <;>
        simp [h]
    rw [hfun, uniformMean_const_mul]
  have houter :
      (fun x : EdgeTuple V k =>
        uniformMean (fun e : Pair V =>
          if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
          then c * F (k + 1) (tupleGraph x) e else 0)) =
      (fun x : EdgeTuple V k => c * uniformMean (fun e : Pair V =>
        if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
        then F (k + 1) (tupleGraph x) e else 0)) := by
    funext x
    exact hinner x
  rw [houter, uniformMean_const_mul]

/-- The terminal cap rescaling follows from the scalar minimum estimate and
terminal-functional monotonicity. -/
theorem S4_RED_14AStatement_of_deps
    (halg : S4_ALG_01Statement)
    (hbridge : S4_BRIDGE_01CStatement) :
    S4_RED_14AStatement := by
  intro q n hq hn L U hLU a w ha haw
  change terminalReal (V := Fin n) q L U
      (fun _ G _ => min w (lifetimeReal q G)) ≤
    (w / a) * terminalReal (V := Fin n) q L U
      (fun _ G _ => min a (lifetimeReal q G))
  rcases hbridge q n hq hn L U hLU with ⟨_, _, hmono⟩
  let F : ℕ → MGraph (Fin n) → Pair (Fin n) → ℝ :=
    fun _ G _ => min w (lifetimeReal q G)
  let J : ℕ → MGraph (Fin n) → Pair (Fin n) → ℝ :=
    fun _ G _ => (w / a) * min a (lifetimeReal q G)
  have hpoint : ∀ h G e, L < h → h ≤ U → Loopless G → Colorable q G →
      ¬ Colorable q (addPair G e) → F h G e ≤ J h G e := by
    intro h G e _ _ _ _ _
    dsimp [F, J]
    exact halg.1 a w (lifetimeReal q G) ha haw (ENNReal.toReal_nonneg)
  calc
    terminalReal q L U F ≤ terminalReal q L U J := hmono F J hpoint
    _ = (w / a) * terminalReal q L U
          (fun _ G _ => min a (lifetimeReal q G)) := by
      rw [terminalReal_const_mul]
  
end ThLean.W.S439

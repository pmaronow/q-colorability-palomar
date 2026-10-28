import ThLean.BP.S4.Bridges

/-!
The finite-average helpers `uniformMean_mul_left`
match implementation patterns in OpenAI's math library (Apache-2.0).
Local versions use project-specific averaging definitions and namespaces.
Their source credits and licence scope are listed in NOTICE; the licence
text is in LICENSES/Apache-2.0.txt.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S424
open ThresholdFoundations ThLean.BP.S4

private theorem uniformMean_mul_left {A : Type} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun x => c * f x) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

private theorem terminalReal_mul_left {V : Type} [Fintype V]
    (q L U : ℕ) (c : ℝ) (a : MGraph V → ℝ) :
    terminalReal q L U (fun _ G _ => c * a G) =
      c * terminalReal q L U (fun _ G _ => a G) := by
  unfold terminalReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← uniformMean_mul_left]
  apply congrArg uniformMean
  funext x
  rw [← uniformMean_mul_left]
  apply congrArg uniformMean
  funext e
  by_cases hterm : Colorable q (tupleGraph x) ∧
      ¬ Colorable q (addPair (tupleGraph x) e)
  · simp [hterm]
  · simp [hterm]

theorem S4_RED_10BStatement_of_deps
    (ha : S4_RED_10AStatement)
    (hb : S4_BRIDGE_01CStatement) :
    S4_RED_10BStatement := by
  intro q n hq hn L U hLU
  let F : ℕ → MGraph (Fin n) → Pair (Fin n) → ℝ :=
    fun h G _ => (h : ℝ) * (2 * truncatedLifetime q (U + 1 - h) G - 1)
  let J : ℕ → MGraph (Fin n) → Pair (Fin n) → ℝ :=
    fun _ G _ => 2 * U * min ((U : ℝ) - L) (lifetimeReal q G)
  have hpoint : ∀ (h : ℕ) (G : MGraph (Fin n)) (e : Pair (Fin n)),
      L < h → h ≤ U → Loopless G → Colorable q G →
      ¬ Colorable q (addPair G e) →
      (h : ℝ) * (2 * truncatedLifetime q (U + 1 - h) G - 1) ≤
        2 * U * min ((U : ℝ) - L) (lifetimeReal q G) := by
    intro h G e hLh hhU hloop hcol hfail
    exact (ha q n hq hn L U h hLh hhU G e hloop hcol hfail).2.2.2
  have hterminal : terminalReal q L U F ≤ terminalReal q L U J :=
    (hb q n hq hn L U hLU).2.2 F J (by
      intro h G e hLh hhU hloop hcol hfail
      exact hpoint h G e hLh hhU hloop hcol hfail)
  have hfactor : terminalReal q L U J =
      2 * U * cappedMoment q n L U ((U : ℝ) - L) := by
    dsimp [J, cappedMoment]
    exact terminalReal_mul_left q L U (2 * (U : ℝ))
      (fun G => min ((U : ℝ) - L) (lifetimeReal q G))
  calc
    deletionMoment q n L U = terminalReal q L U F := rfl
    _ ≤ terminalReal q L U J := hterminal
    _ = 2 * U * cappedMoment q n L U ((U : ℝ) - L) := hfactor

example (ha : S4_RED_10AStatement) (hb : S4_BRIDGE_01CStatement) :
    S4_RED_10BStatement := S4_RED_10BStatement_of_deps ha hb

end ThLean.W.S424

module

public import ThLean.BP.S3.Poisson

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S341

open ThresholdFoundations

private theorem poissonMixture_zero_eval (a : ℕ → ℝ) :
    poissonMixture 0 a = a 0 := by
  unfold poissonMixture
  have hz : ∀ n ≠ 0, poissonWeight 0 n * a n = 0 := by
    intro n hn
    simp [poissonWeight, hn]
  rw [tsum_eq_single 0 hz]
  simp [poissonWeight]

private theorem poissonGraphMean_zero_at_zero {W : Type*} [Fintype W]
    (H : MGraph W) :
    poissonGraphMean 0 (fun G => indicator (G = H)) = indicator (H = 0) := by
  unfold poissonGraphMean
  rw [poissonMixture_zero_eval]
  have hzero : ∀ x : EdgeTuple W 0, tupleGraph x = (0 : MGraph W) := by
    intro x
    funext e
    simp [tupleGraph]
  simp [uniformMean, hzero, indicator, eq_comm]

theorem S3_37bStatement_holds : ThLean.BP.S3.S3_37bStatement := by
  intro V instV S hS
  constructor
  · intro G hG
    funext e
    induction e using Sym2.ind with
    | h a b =>
      have habval : a.val = b.val :=
        Finset.card_le_one_iff.mp hS a.property b.property
      have hab : a = b := Subtype.ext habval
      subst b
      simpa [inducedGraph] using hG a.val
  · intro H
    exact poissonGraphMean_zero_at_zero H

end ThLean.W.S341

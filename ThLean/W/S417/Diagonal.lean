import ThLean.BP.S4.Deletion

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S417

open ThresholdFoundations

theorem S4_RED_04BStatement_of_deps
    (hA : ThLean.BP.S4.S4_RED_04AStatement) :
    ThLean.BP.S4.S4_RED_04BStatement := by
  intro q n hq hn T m i hi hm
  have hdiag := hA q n hq hn T m m i hi le_rfl hm (fun _ => 1)
  have hleft :
      (fun x : EdgeTuple (Fin n) T =>
        (1 : ℝ) * indicator (deletionDisagreement q x i m) *
          indicator (Colorable q (deletedPrefix x i m))) =
      (fun x => indicator (deletionDisagreement q x i m)) := by
    funext x
    by_cases hd : Colorable q (deletedPrefix x i m) <;>
      simp [indicator, deletionDisagreement, hd]
  have hkappa_survival (G : MGraph (Fin n)) :
      kappa q G * survival q G 0 = kappa q G := by
    by_cases hc : Colorable q G
    · have hs : survival q G 0 = 1 := by
        have hG : ∀ x : EdgeTuple (Fin n) 0, G + tupleGraph x = G := by
          intro x
          have hx : x = (default : EdgeTuple (Fin n) 0) := Subsingleton.elim _ _
          subst x
          have ht : tupleGraph (default : EdgeTuple (Fin n) 0) = 0 := by
            funext e
            simp [tupleGraph]
          rw [ht]
          funext e
          simp
        simp [survival, uniformProb, uniformMean, indicator, hG, hc]
      rw [hs]
      ring
    · have hk : kappa q G = 0 := by
        simp [kappa, uniformProb, uniformMean, indicator, FrozenPair, Frozen, hc]
      rw [hk]
      ring
  have hright :
      (fun x : EdgeTuple (Fin n) (m - 1) =>
        (1 : ℝ) * kappa q (tupleGraph x) *
          survival q (tupleGraph x) (m - m)) =
      (fun x => kappa q (tupleGraph x)) := by
    funext x
    have hm0 : m - m = 0 := Nat.sub_self m
    rw [hm0]
    simpa using hkappa_survival (tupleGraph x)
  rw [hleft, hright] at hdiag
  exact hdiag

end ThLean.W.S417

import ThLean.BP.S4.Bridges
import ThLean.Contrib.S436.PreLifetimeDependency

noncomputable section
open scoped BigOperators ENNReal
namespace ThLean.W.S436
open ThresholdFoundations

/-- The S4 lifetime bridge follows from the upstream pre-lifetime contract. -/
theorem S4_BRIDGE_03AStatement_from_preLifetime
    (hpre : ThLean.Contrib.S436.PreLifetimeDependencyStatement) :
    ThLean.BP.S4.S4_BRIDGE_03AStatement := by
  change ThresholdFoundations.PreLifetimeStatement.{0} at hpre
  intro q n hq hn G hG
  have hV : 2 ≤ Fintype.card (Fin n) := by simp only [Fintype.card_fin]; omega
  have hGpre := (hpre (Fin n) q hq hV).1 G hG
  rcases hGpre with ⟨hzero, _, _, _, hlarge⟩
  have hnq : 2*q ≤ Fintype.card (Fin n) := by simpa using hn
  rcases hlarge hnq with ⟨_, hfinite, hsum, hreal⟩
  refine ⟨hfinite, hsum, hreal.symm, ?_, ?_, ?_⟩
  · intro y hy
    exact ENNReal.ofReal_lt_iff_lt_toReal hy (ne_of_lt hfinite)
  · intro a ha
    rw [ENNReal.toReal_min ENNReal.ofReal_ne_top (ne_of_lt hfinite)]
    simp [ENNReal.toReal_ofReal ha, lifetimeReal]
  · intro hnot
    have hz := (hzero hnot).1
    exact ⟨hz, by simp [lifetimeReal, hz]⟩

end ThLean.W.S436

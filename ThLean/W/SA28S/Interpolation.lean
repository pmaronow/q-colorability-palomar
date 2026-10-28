import ThLean.W.SA28S.EndpointSeries
import ThLean.W.SA28.Interpolation

noncomputable section

namespace ThLean.W.SA28S
open ThresholdFoundations ThLean.BP.SA

/-- The interpolation endpoints, zero rate, and singleton law, using only the
permitted analytic bridge leaf as a premise. -/
theorem SA_I13bStatement_of_deps (h13a : ThLean.BP.SA.SA_I13aStatement) :
    ThLean.BP.SA.SA_I13bStatement := by
  apply ThLean.W.SA28.SA_I13bStatement_of_endpoints
  intro q n₁ n₂ hq h₁ h₂ c _hc
  constructor
  · rw [finiteChi, ← (h13a q n₁ n₂ hq h₁ h₂ (interpolationMeans n₁ n₂ c 0)).2]
    exact chiBar_local q n₁ n₂ h₁ h₂ c
  · rw [finiteChi, ← (h13a q n₁ n₂ hq h₁ h₂ (interpolationMeans n₁ n₂ c c)).2]
    exact chiBar_global q n₁ n₂ c

example (h13a : ThLean.BP.SA.SA_I13aStatement) : ThLean.BP.SA.SA_I13bStatement :=
  SA_I13bStatement_of_deps h13a

end ThLean.W.SA28S

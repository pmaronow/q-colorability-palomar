module

public import ThLean.BP.S4.Bridges

@[expose] public section

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.S434
open ThresholdFoundations ThLean.BP.S4

/-- The finite terminal probability over an interval is at most one. -/
def S4_BRIDGE_01CNormalizationStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    terminalProb (V := Fin n) q L U (fun _ _ => True) ≤ 1

end ThLean.Contrib.S434

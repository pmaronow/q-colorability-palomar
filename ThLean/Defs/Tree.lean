module

public import ThLean.Defs.Probability

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

inductive BlockTree where
  | leaf (size : ℕ)
  | node (left right : BlockTree)

namespace BlockTree
def size : BlockTree → ℕ
  | .leaf n => n
  | .node a b => size a + size b
def leaves : BlockTree → ℕ
  | .leaf _ => 1
  | .node a b => leaves a + leaves b
def height : BlockTree → ℕ
  | .leaf _ => 0
  | .node a b => max (height a) (height b) + 1
def Balanced (ℓ : ℕ) : BlockTree → Prop
  | .leaf n => n = ℓ ∨ n = ℓ + 1
  | .node a b => Balanced ℓ a ∧ Balanced ℓ b ∧
      leaves a = (leaves a + leaves b + 1) / 2 ∧
      leaves b = (leaves a + leaves b) / 2
end BlockTree

end ThresholdFoundations

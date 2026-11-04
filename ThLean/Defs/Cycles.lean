module

public import ThLean.Defs.Graph

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

variable {V : Type*} [Fintype V]

/-! ## Occurrence paths and cycles, Lemma pre-cycles -/

structure OccurrencePath (G : MGraph V) where
  length : ℕ
  vertex : Fin (length + 1) → V
  edge : Fin length → Occurrence G
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  joins : ∀ i : Fin length, (edge i).1 = s(vertex ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩,
     vertex ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

def pathVertices {G : MGraph V} (p : OccurrencePath G) : Finset V :=
  Finset.univ.image p.vertex
def pathOccurrences {G : MGraph V} (p : OccurrencePath G) : Finset (Occurrence G) :=
  Finset.univ.image p.edge
def PathFrom {G : MGraph V} (p : OccurrencePath G) (a b : V) : Prop :=
  p.vertex ⟨0, Nat.zero_lt_succ _⟩ = a ∧
    p.vertex ⟨p.length, Nat.lt_succ_self _⟩ = b

structure OccurrenceCycle (G : MGraph V) where
  length : ℕ
  length_ge_two : 2 ≤ length
  vertex : Fin length → V
  edge : Fin length → Occurrence G
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  joins : ∀ i : Fin length, (edge i).1 = s(vertex i, vertex ⟨(i.val + 1) % length, Nat.mod_lt _ (by omega)⟩)

def cycleVertices {G : MGraph V} (c : OccurrenceCycle G) : Finset V :=
  Finset.univ.image c.vertex
def cycleOccurrences {G : MGraph V} (c : OccurrenceCycle G) : Finset (Occurrence G) :=
  Finset.univ.image c.edge

/-- Three internally vertex-disjoint, occurrence-disjoint positive paths. -/
def ThetaIn (G : MGraph V) : Prop :=
  ∃ a b : V, a ≠ b ∧ ∃ p₁ p₂ p₃ : OccurrencePath G,
    (∀ p ∈ [p₁, p₂, p₃], 1 ≤ p.length ∧ PathFrom p a b) ∧
    [p₁, p₂, p₃].Pairwise (fun p r =>
      Disjoint (pathOccurrences p) (pathOccurrences r) ∧
      pathVertices p ∩ pathVertices r ⊆ {a, b})

/-- The joining path in the disjoint-cycle case meets each cycle only at its
endpoint. The other case allows exactly one common vertex and no shared edge. -/
def DumbbellIn (G : MGraph V) : Prop :=
  ∃ c₁ c₂ : OccurrenceCycle G,
    Disjoint (cycleOccurrences c₁) (cycleOccurrences c₂) ∧
    ((cycleVertices c₁ ∩ cycleVertices c₂).card = 1 ∨
      (Disjoint (cycleVertices c₁) (cycleVertices c₂) ∧
        ∃ (p : OccurrencePath G) (a b : V),
          1 ≤ p.length ∧ PathFrom p a b ∧ a ∈ cycleVertices c₁ ∧ b ∈ cycleVertices c₂ ∧
          pathVertices p ∩ cycleVertices c₁ = {a} ∧
          pathVertices p ∩ cycleVertices c₂ = {b} ∧
          Disjoint (pathOccurrences p) (cycleOccurrences c₁ ∪ cycleOccurrences c₂)))

/-- Connectivity on vertices that occur in an edge; isolated vertices do not
affect the `v(K)` used by Lemma pre-cycles. -/
def ConnectedSupport (G : MGraph V) : Prop :=
  ∀ a ∈ vertexSupport G, ∀ b ∈ vertexSupport G,
    ∃ p : OccurrencePath G, PathFrom p a b

end ThresholdFoundations

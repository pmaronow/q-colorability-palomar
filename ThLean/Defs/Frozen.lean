module

public import ThLean.Defs.Graph

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

variable {V : Type*} [Fintype V]

/-! ## Frozen classes and the high-degree objects -/

/-- Def. pre-frozen. The colorability guard prevents vacuous freezing. -/
def Frozen (q : ℕ) (G : MGraph V) (u v : V) : Prop :=
  Colorable q G ∧ ∀ σ, IsColoring q G σ → σ u = σ v

def frozenClass (q : ℕ) (G : MGraph V) (u : V) : Finset V :=
  Finset.univ.filter (Frozen q G u)

def FrozenPair (q : ℕ) (G : MGraph V) (e : Pair V) : Prop :=
  ∃ u v, e.val = s(u, v) ∧ Frozen q G u v

def inFrozenPair (q : ℕ) (G : MGraph V) (u : V) : Prop :=
  2 ≤ (frozenClass q G u).card

def frozenClasses (q : ℕ) (G : MGraph V) : Finset (Finset V) :=
  (Finset.univ.image (frozenClass q G)).filter (fun C => C.Nonempty)

def kappa (q : ℕ) (G : MGraph V) : ℝ := uniformProb (FrozenPair q G)

def classMass (q : ℕ) (G : MGraph V) : ℝ :=
  ∑ C ∈ frozenClasses q G, ((C.card : ℝ) / (Fintype.card V : ℝ)) ^ 2

/-- Eq. pre-kappaE; the guard enforces the admissibility of a terminal kind. -/
def kappaKind (q : ℕ) (A : MGraph V → Pair V → Prop) (G : MGraph V) : ℝ :=
  uniformProb (fun e => FrozenPair q G e ∧ A G e)

def relabelInvariant (f : MGraph V → ℝ) : Prop :=
  ∀ (π : Equiv.Perm V) G, f (relabel π G) = f G

def kindInvariant (A : MGraph V → Pair V → Prop) : Prop :=
  ∀ (π : Equiv.Perm V) G e e', Sym2.map π e.val = e'.val →
    (A (relabel π G) e' ↔ A G e)

end ThresholdFoundations

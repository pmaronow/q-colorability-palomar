module

public import ThLean.Defs.Probability

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

/-- Def. pre-multigraph. Unordered pairs; the predicate excludes the diagonal. -/
abbrev Pair (V : Type*) := {e : Sym2 V // ∀ v : V, e ≠ s(v, v)}

/-- Finite-vertex multiplicity function. The carrier also admits loops so
identification and Appendix A use exactly the same representation.
The paper's ordinary multigraphs satisfy `Loopless`. -/
abbrev MGraph (V : Type*) := Sym2 V → ℕ

def Loopless {V : Type*} (G : MGraph V) : Prop :=
  ∀ v : V, G (s(v, v)) = 0

def Touches {V : Type*} (u : V) (e : Sym2 V) : Prop :=
  ∃ v : V, e = s(u, v)

abbrev Occurrence {V : Type*} (G : MGraph V) := Σ e : Sym2 V, Fin (G e)

def subgraph {V : Type*} (G F : MGraph V) : Prop := ∀ e, G e ≤ F e

def addEdge {V : Type*} (G : MGraph V) (e : Sym2 V) : MGraph V :=
  Function.update G e (G e + 1)

/-- Total extension; the paper uses this only when `0 < G e`. -/
def eraseEdge {V : Type*} (G : MGraph V) (e : Sym2 V) : MGraph V :=
  Function.update G e (G e - 1)

def addPair {V : Type*} (G : MGraph V) (e : Pair V) : MGraph V := addEdge G e.val
def erasePair {V : Type*} (G : MGraph V) (e : Pair V) : MGraph V := eraseEdge G e.val

variable {V : Type*} [Fintype V]

def edgeCount (G : MGraph V) : ℕ := ∑ e, G e
def edgeSupport (G : MGraph V) : Finset (Sym2 V) := Finset.univ.filter (0 < G ·)
def vertexSupport (G : MGraph V) : Finset V :=
  Finset.univ.filter (fun u => ∃ e, 0 < G e ∧ Touches u e)

/-- Def. pre-multigraph: occurrence degree. A loop counts once here;
all degree lemmas of the paper have `Loopless G` as a hypothesis. -/
def degree (G : MGraph V) (u : V) : ℕ :=
  ∑ e, if Touches u e then G e else 0

def IsColoring (q : ℕ) (G : MGraph V) (σ : V → Fin q) : Prop :=
  ∀ u v : V, 0 < G (s(u, v)) → σ u ≠ σ v

def colorings (q : ℕ) (G : MGraph V) : Finset (V → Fin q) :=
  Finset.univ.filter (IsColoring q G)

def Colorable (q : ℕ) (G : MGraph V) : Prop := ∃ σ, IsColoring q G σ

/-- Relabeling, including noninjective maps. Collisions ADD multiplicities. -/
def mapGraph {W : Type*} [Fintype W] (f : V → W) (G : MGraph V) : MGraph W :=
  fun e' => ∑ e, if Sym2.map f e = e' then G e else 0

/-- Induced graph on an actual subtype, without leaving ghost vertices. -/
def inducedGraph (G : MGraph V) (S : Finset V) : MGraph {v : V // v ∈ S} :=
  fun e => G (Sym2.map Subtype.val e)

def relabel {W : Type*} [Fintype W] (e : V ≃ W) (G : MGraph V) : MGraph W :=
  mapGraph e G

end ThresholdFoundations

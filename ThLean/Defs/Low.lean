import ThLean.Defs.Process

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

variable {V : Type*} [Fintype V]

/-! ## Identification and neighbor lists, Section 5 -/

def constantOn {q : ℕ} (σ : V → Fin q) (Z : Finset V) : Prop :=
  ∀ u ∈ Z, ∀ v ∈ Z, σ u = σ v

def neverMonochromatic (q : ℕ) (B : MGraph V) (xs : List V) : Prop :=
  Colorable q B ∧ ∀ σ, IsColoring q B σ → 2 ≤ (xs.map σ).toFinset.card

def nmProbability (q D : ℕ) (B : MGraph V) : ℝ :=
  uniformProb (fun x : Fin D → V => neverMonochromatic q B (List.ofFn x))

abbrev QuotientVertices (Z : Finset V) := Option {v : V // v ∉ Z}

/-- `none` is the new vertex o. Identification theorems assume Z nonempty. -/
def identifyVertex (Z : Finset V) (v : V) : QuotientVertices Z :=
  if h : v ∈ Z then none else some ⟨v, h⟩

def identify (B : MGraph V) (Z : Finset V) : MGraph (QuotientVertices Z) :=
  mapGraph (identifyVertex Z) B

def star (xs : List V) : MGraph (Option V) :=
  fun e => (xs.map (fun v => s(none, some v))).count e

def addRoot (B : MGraph V) (xs : List V) : MGraph (Option V) :=
  mapGraph some B + star xs

def otherEndpoint (a : V) (e : Sym2 V) (h : Touches a e) : V := Classical.choose h

/-- Arbitrary deterministic occurrence order; structural lemmas do not use it. -/
def neighborList (G : MGraph V) (a : V) : List V :=
  (Finset.univ : Finset (Occurrence G)).toList.filterMap (fun o =>
    if h : Touches a o.1 then some (otherEndpoint a o.1 h) else none)

/-- Chronological list: paper's neighbor list at a fixed Poisson time. -/
def neighborPrefix (ω : EdgeStream V) (m : ℕ) (a : V) (S : Finset V) : List V :=
  (List.ofFn (fun i : Fin m => ω i.val)).filterMap (fun e =>
    if h : Touches a e.val then
      let v := otherEndpoint a e.val h
      if v ∈ S then some v else none
    else none)

def identifiedHittingTime (q : ℕ) (Z : Finset V) (ω : EdgeStream V) : WithTop ℕ :=
  firstFailure (fun m => ¬ Colorable q (identify (processGraph ω m) Z))

def addedRootHittingTime (q : ℕ) (B : MGraph V) (x : ℕ → V) : WithTop ℕ :=
  firstFailure (fun k => ¬ Colorable q (addRoot B (List.ofFn (fun i : Fin k => x i.val))))

abbrev UniformSubset (V : Type*) [Fintype V] (D : ℕ) := {Z : Finset V // Z.card = D}

abbrev CompletionSubset (xs : List V) (D : ℕ) :=
  {Z : Finset V // xs.toFinset ⊆ Z ∧ Z.card = D}

def identificationFailureProbability (q D : ℕ) (B : MGraph V) : ℝ :=
  uniformProb (fun Z : UniformSubset V D => Colorable q B ∧ ¬ Colorable q (identify B Z.val))

/-- Nonnegative version of E[H-H_Z], valid without infinity-minus-infinity. -/
def identificationAdvance (q D : ℕ) : ℝ≥0∞ :=
  ∑' m : ℕ, uniformMeanENN (fun x : EdgeTuple V m =>
      uniformMeanENN (fun Z : UniformSubset V D =>
        if Colorable q (tupleGraph x) ∧ ¬ Colorable q (identify (tupleGraph x) Z.val)
        then 1 else 0))

end ThresholdFoundations

import ThLean.Defs.Process

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

variable {V : Type*} [Fintype V]

/-! ## Simple graph models used at the transfer interface -/

def completeEdges : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => ∀ v : V, e ≠ s(v, v))
def simpleGraph (E : Finset (Sym2 V)) : MGraph V := fun e => if e ∈ E then 1 else 0
def simpleGraphsWithEdges (m : ℕ) : Finset (Finset (Sym2 V)) :=
  (completeEdges (V := V)).powerset.filter (fun E => E.card = m)
def simpleProbability (q m : ℕ) : ℝ :=
  (((simpleGraphsWithEdges (V := V) m).filter
    (fun E => Colorable q (simpleGraph E))).card : ℝ) /
    ((simpleGraphsWithEdges (V := V) m).card : ℝ)
def bernoulliProbability (q : ℕ) (p : ℝ) : ℝ :=
  ∑ E ∈ (completeEdges (V := V)).powerset,
    p ^ E.card * (1 - p) ^ ((Fintype.card V).choose 2 - E.card) *
      indicator (Colorable q (simpleGraph E))
def DistinctPrefix {m : ℕ} (x : EdgeTuple V m) : Prop := Function.Injective x

end ThresholdFoundations

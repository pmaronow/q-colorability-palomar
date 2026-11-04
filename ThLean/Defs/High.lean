module

public import ThLean.Defs.Frozen

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

variable {V : Type*} [Fintype V]

/-- Def. high-pivotal. Every parallel copy is counted separately. -/
def nonpivotalCount (q : ℕ) (G : MGraph V) (u v : V) : ℕ :=
  ∑ e, if Touches u e ∧ Frozen q G u v ∧ Frozen q (eraseEdge G e) u v
    then G e else 0

def Nonpivotal (q : ℕ) (G : MGraph V) (u v : V) (o : Occurrence G) : Prop :=
  Touches u o.1 ∧ Frozen q G u v ∧ Frozen q (eraseEdge G o.1) u v

def Pivotal (q : ℕ) (G : MGraph V) (u v : V) (o : Occurrence G) : Prop :=
  Touches u o.1 ∧ Frozen q G u v ∧ ¬ Frozen q (eraseEdge G o.1) u v

def kappaDegree (q j : ℕ) (G : MGraph V) : ℝ :=
  (∑ u : V, ∑ v : V, indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j)) /
    ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))

def kappaDegreeNP (q K j : ℕ) (G : MGraph V) : ℝ :=
  (∑ u : V, ∑ v : V, indicator
    (u ≠ v ∧ Frozen q G u v ∧ degree G u = j ∧ K ≤ nonpivotalCount q G u v)) /
    ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))

/-- Direct count of the complement, avoiding subtraction of probabilities. -/
def kappaDegreePiv (q K j : ℕ) (G : MGraph V) : ℝ :=
  (∑ u : V, ∑ v : V, indicator
    (u ≠ v ∧ Frozen q G u v ∧ degree G u = j ∧ nonpivotalCount q G u v < K)) /
    ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))

/-- The function h in the proof of lem:high-deletion(a). -/
def nonpivotalDeletionCount (q j : ℕ) (G : MGraph V) (e : Pair V) : ℝ :=
  ∑ a : V, ∑ v : V, indicator (Touches a e.val ∧ a ≠ v ∧
    Frozen q (addPair G e) a v ∧ Frozen q G a v ∧ degree (addPair G e) a = j)

/-- The function h' in the proof of lem:high-deletion(b). -/
def pivotalDeletionCount (q j : ℕ) (G : MGraph V) (e : Pair V) : ℝ :=
  ∑ a : V, ∑ v : V, indicator (Touches a e.val ∧ a ≠ v ∧
    Frozen q (addPair G e) a v ∧ ¬ Frozen q G a v ∧ degree G a = j - 1)

/-- Def. high-relation, including the empty value off the colorable event. -/
def relation (q : ℕ) (G : MGraph V) (u : V) : Finset (V × V) :=
  Finset.univ.filter (fun yv => Colorable q G ∧
    ¬ Frozen q G u yv.1 ∧ ¬ Frozen q G u yv.2 ∧
    ∀ σ, IsColoring q G σ → (σ u = σ yv.1 ∨ σ u = σ yv.2))

def relationSection (q : ℕ) (G : MGraph V) (u y : V) : Finset V :=
  Finset.univ.filter (fun v => (y, v) ∈ relation q G u)

def beta (q : ℕ) (G : MGraph V) (u : V) : ℝ :=
  ((relation q G u).card : ℝ) / (Fintype.card V : ℝ) ^ 2

def creditedAt (q : ℕ) (G : MGraph V) (u a b : V) : Finset V :=
  if ¬ Colorable q G then ∅ else
  if Frozen q G u a then
    if Frozen q G u b then ∅ else relationSection q G u b
  else if Frozen q G u b then relationSection q G u a
  else relationSection q G u a ∩ relationSection q G u b

/-- Def. high-credited. Taking the symmetric endpoint representatives avoids
choosing an ordering of an unordered edge. No guard on `G+f` is permitted. -/
def credited (q : ℕ) (G : MGraph V) (u : V) (f : Pair V) : Finset V :=
  Finset.univ.filter (fun v => ∃ a b,
    f.val = s(a, b) ∧ v ∈ creditedAt q G u a b)

def potential (q : ℕ) (G : MGraph V) (u : V) : ℝ :=
  if Colorable q G then Real.log ((frozenClass q G u).card : ℝ) else 0

def creditIncrement (q : ℕ) (G : MGraph V) (u : V) (f : Pair V) : ℝ :=
  if Colorable q G then
    Real.log (1 + ((credited q G u f).card : ℝ) / ((frozenClass q G u).card : ℝ))
  else 0

def directCreditSum (q : ℕ) (G : MGraph V) (u : V) : ℝ :=
  ∑ a ∈ Finset.univ \ frozenClass q G u,
    ∑ b ∈ Finset.univ \ frozenClass q G u,
      min (((relationSection q G u a ∩ relationSection q G u b).card : ℝ) /
        ((frozenClass q G u).card : ℝ)) 1

def crossCreditSum (q : ℕ) (G : MGraph V) (u : V) : ℝ :=
  2 * (((frozenClass q G u).card : ℝ) - 1) *
    ∑ a ∈ Finset.univ \ frozenClass q G u,
      min (((relationSection q G u a).card : ℝ) / ((frozenClass q G u).card : ℝ)) 1

end ThresholdFoundations

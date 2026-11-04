module

public import ThLean.Defs

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations


/-! Auxiliary vocabulary for closed Section 3 statements. -/

def graphProb {V : Type u} [Fintype V] (m : ℕ) (P : MGraph V → Prop) : ℝ :=
  uniformProb (fun x : EdgeTuple V m => P (tupleGraph x))

def initTuple {V : Type u} {m : ℕ} (x : EdgeTuple V (m+1)) : EdgeTuple V m :=
  fun i => x i.castSucc

def lastPair {V : Type u} {m : ℕ} (x : EdgeTuple V (m+1)) : Pair V := x (Fin.last m)

def natCDF {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ) (m : ℕ) : ℝ :=
  μ.real {ω | X ω ≤ m}

def natTail {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ) (m : ℕ) : ℝ :=
  μ.real {ω | m ≤ X ω}

def lawLower {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ)
    (M : ℕ) (η : ℝ) : ℕ :=
  if h : ∃ m, m ≤ M ∧ η ≤ natCDF μ X m then Nat.find h else M

def lawUpper {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ)
    (M : ℕ) (η : ℝ) : ℕ :=
  M - (if h : ∃ k, k ≤ M ∧ η ≤ natTail μ X (M-k) then Nat.find h else M)

def AdmissibleKind {V : Type u} [Fintype V] (q : ℕ)
    (A : MGraph V → Pair V → Prop) : Prop :=
  ∀ G e, A G e → FrozenPair q G e

def RelabelInvariantENN {V : Type u} [Fintype V] (h : MGraph V → ℝ≥0∞) : Prop :=
  ∀ (π : Equiv.Perm V) G, h (relabel π G) = h G

def terminalSetRangeENN {V : Type u} [Fintype V] (q : ℕ)
    (J : Set ℕ) (A : MGraph V → Pair V → Prop)
    (h : ℕ → MGraph V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' m : ℕ, if m ∈ J then
    terminalStepENN q m (fun G e => if A G e then h m G else 0) else 0

def monoPairProb {V : Type u} [Fintype V] {q : ℕ} (σ : V → Fin q) : ℝ :=
  uniformProb (fun e : Pair V => ∃ u v, e.val = s(u,v) ∧ σ u = σ v)

def colorClassSize {V : Type u} [Fintype V] {q : ℕ} (σ : V → Fin q) (i : Fin q) : ℕ :=
  (Finset.univ.filter (fun v => σ v = i)).card

def poissonEvent (z : ℝ) (P : ℕ → Prop) : ℝ :=
  (∑' k : ℕ, if P k then ENNReal.ofReal (poissonWeight z k) else 0).toReal

def cellMass {E : Type u} [Fintype E] {J : ℕ} (ν : E → ℝ)
    (label : E → Fin J) (j : Fin J) : ℝ :=
  ∑ e, if label e = j then ν e else 0

def IsProbabilityVector {E : Type u} [Fintype E] (ν : E → ℝ) : Prop :=
  (∀ e, 0 ≤ ν e) ∧ ∑ e, ν e = 1

def listGraph {V : Type u} [Fintype V] (xs : List (Pair V)) : MGraph V :=
  fun e => (xs.filter (fun p => p.val = e)).length

def poissonListMeanENN {E : Type u} [Fintype E]
    (z : ℝ) (ν : E → ℝ) (f : List E → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' xs : List E, ENNReal.ofReal (poissonListMass z ν xs) * f xs

def poissonWordProb {V : Type u} [Fintype V] (z : ℝ) (P : List (Pair V) → Prop) : ℝ :=
  poissonMixture z (fun m => uniformProb (fun x : EdgeTuple V m => P (List.ofFn x)))

def pairRate {V : Type u} (rate : ℝ) (e : Sym2 V) : ℝ :=
  if ∃ v, e = s(v,v) then 0 else rate

def neighborList {V : Type u} [Fintype V] (a : V) (S : Finset V)
    (xs : List (Pair V)) : List V :=
  xs.filterMap (fun e => if h : ∃ v ∈ S, e.val = s(a,v) then
    some (Classical.choose h) else none)

def graphSupport {V : Type u} [Fintype V] (G : MGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ 0 < G s(u,v)
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

def SpanningTree {V : Type u} [Fintype V] (T G : MGraph V) : Prop :=
  Loopless T ∧ subgraph T G ∧ (∀ e, T e ≤ 1) ∧ (graphSupport T).IsTree

def OccLift {V : Type u} {T G : MGraph V} (h : subgraph T G) : Occurrence T → Occurrence G :=
  fun e => ⟨e.1, ⟨e.2.val, lt_of_lt_of_le e.2.isLt (h e.1)⟩⟩

def ExactTheta {V : Type u} [Fintype V] (G : MGraph V) : Prop :=
  ∃ a b : V, a ≠ b ∧ ∃ p₁ p₂ p₃ : OccurrencePath G,
    (∀ p ∈ [p₁,p₂,p₃], 1 ≤ p.length ∧ PathFrom p a b) ∧
    [p₁,p₂,p₃].Pairwise (fun p r =>
      Disjoint (pathOccurrences p) (pathOccurrences r) ∧
      pathVertices p ∩ pathVertices r ⊆ {a,b}) ∧
    pathOccurrences p₁ ∪ pathOccurrences p₂ ∪ pathOccurrences p₃ = Finset.univ

def ExactDumbbell {V : Type u} [Fintype V] (G : MGraph V) : Prop :=
  ∃ c₁ c₂ : OccurrenceCycle G,
    Disjoint (cycleOccurrences c₁) (cycleOccurrences c₂) ∧
    (((cycleVertices c₁ ∩ cycleVertices c₂).card = 1 ∧
       cycleOccurrences c₁ ∪ cycleOccurrences c₂ = Finset.univ) ∨
      (Disjoint (cycleVertices c₁) (cycleVertices c₂) ∧
        ∃ (p : OccurrencePath G) (a b : V),
          1 ≤ p.length ∧ PathFrom p a b ∧ a ∈ cycleVertices c₁ ∧ b ∈ cycleVertices c₂ ∧
          pathVertices p ∩ cycleVertices c₁ = {a} ∧
          pathVertices p ∩ cycleVertices c₂ = {b} ∧
          Disjoint (pathOccurrences p) (cycleOccurrences c₁ ∪ cycleOccurrences c₂) ∧
          cycleOccurrences c₁ ∪ cycleOccurrences c₂ ∪ pathOccurrences p = Finset.univ))

def Witness {V : Type u} [Fintype V] (k : ℕ) (G : MGraph V) : Prop :=
  Loopless G ∧ (vertexSupport G).card = k ∧ (ExactTheta G ∨ ExactDumbbell G)

def obstructionSeries (a : ℝ) : ℝ := ∑' j : ℕ, ((j+4 : ℕ) : ℝ)^2 * a^(j+3)
def obstructionConstant (c : ℝ) : ℝ := 4 * Real.exp 2 * obstructionSeries (2*c)


def edgesGraph {V : Type u} [Fintype V] (xs : List (Sym2 V)) : MGraph V :=
  fun e => (xs.filter (fun f => f=e)).length

def consecutiveEdges {V : Type u} (xs : List V) : List (Sym2 V) :=
  (xs.zip xs.tail).map (fun p => s(p.1,p.2))

def codeLabel {V : Type u} {k : ℕ} (hk : 0 < k) (v : Fin k → V) (i : ℕ) : V :=
  v ⟨i % k, Nat.mod_lt _ hk⟩

def thetaCode {V : Type u} [Fintype V] {k : ℕ} (hk : 0 < k)
    (j₁ j₂ j₃ : ℕ) (labels : Fin k → V) : MGraph V :=
  let v := codeLabel hk labels
  edgesGraph (
    consecutiveEdges ([v 0] ++ ((List.range (j₁-1)).map (fun i => v (2+i))) ++ [v 1]) ++
    consecutiveEdges ([v 0] ++ ((List.range (j₂-1)).map (fun i => v (j₁+1+i))) ++ [v 1]) ++
    consecutiveEdges ([v 0] ++ ((List.range (j₃-1)).map (fun i => v (j₁+j₂+i))) ++ [v 1]))

def dumbbellCode {V : Type u} [Fintype V] {k : ℕ} (hk : 0 < k)
    (j₁ j₂ j₃ : ℕ) (labels : Fin k → V) : MGraph V :=
  let v := codeLabel hk labels
  let c₁ := consecutiveEdges ((List.range j₁).map v ++ [v 0])
  if j₃ = 0 then
    edgesGraph (c₁ ++ consecutiveEdges
      ([v 0] ++ ((List.range (j₂-1)).map (fun i => v (j₁+i))) ++ [v 0]))
  else
    edgesGraph (c₁ ++ consecutiveEdges
      (((List.range j₂).map (fun i => v (j₁+i))) ++ [v j₁]) ++
      consecutiveEdges ([v 0] ++
        ((List.range (j₃-1)).map (fun i => v (j₁+j₂+i))) ++ [v j₁]))

end ThLean.BP.S3

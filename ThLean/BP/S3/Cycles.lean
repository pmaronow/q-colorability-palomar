module

public import ThLean.BP.S3.Tails

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `lem:pre-cycles`; blueprint P1-55. -/
def S3_55Statement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
  ∀ K : MGraph V, Loopless K → (graphSupport K).Connected →
    ∃ T : MGraph V, SpanningTree T K ∧ edgeCount T + 1 = Fintype.card V ∧
      Colorable 2 T ∧ ∀ a b : V, ∃! p : OccurrencePath T, PathFrom p a b

/-- Paper `lem:pre-cycles(a)`; blueprint P1-56. -/
def S3_56Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 3 ≤ q →
  ∀ B : MGraph V, Colorable 2 B →
    Colorable q B ∧ ∀ e : Pair V, Colorable q (addPair B e)

/-- Paper `lem:pre-cycles(a)`; blueprint P1-57a. -/
def S3_57aStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (K T : MGraph V), Loopless K →
    SpanningTree T K → edgeCount T + 1 = Fintype.card V →
    edgeCount K ≤ Fintype.card V → K = T ∨ ∃ e : Pair V, K = addPair T e

/-- Paper `lem:pre-cycles(a)`; blueprint P1-57. -/
def S3_57Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
  ∀ K : MGraph V, Loopless K → (graphSupport K).Connected →
    edgeCount K ≤ Fintype.card V → Colorable q K

theorem S3_57_assembly (h55 : S3_55Statement.{u}) (h56 : S3_56Statement.{u})
    (h57a : S3_57aStatement.{u}) : S3_57Statement.{u} := by
  intro V _ q hq hV K hK hconn hsize
  obtain ⟨T,hT,hcard,hcol,_⟩ := h55 V hV K hK hconn
  rcases h57a V K T hK hT hcard hsize with heq | ⟨e,heq⟩
  · rw [heq]
    exact (h56 V q hq T hcol).1
  · rw [heq]
    exact (h56 V q hq T hcol).2 e

/-- Paper `lem:pre-cycles(b)`; blueprint P1-58. -/
def S3_58Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (K T : MGraph V), Loopless K →
  SpanningTree T K → ∀ h : subgraph T K, ∀ p p' : Occurrence K, p ≠ p' →
    p ∉ Finset.univ.image (OccLift h) → p' ∉ Finset.univ.image (OccLift h) →
    ∃ c d : OccurrenceCycle K,
      cycleOccurrences c \ Finset.univ.image (OccLift h) = {p} ∧
      cycleOccurrences d \ Finset.univ.image (OccLift h) = {p'} ∧
      p' ∉ cycleOccurrences c

/-- Paper `lem:pre-cycles(b)`; blueprint P1-59. -/
def S3_59Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (G : MGraph V) (c : OccurrenceCycle G)
    (a b : V), a ∈ cycleVertices c → b ∈ cycleVertices c → a ≠ b →
    ∃ p r : OccurrencePath G, 1 ≤ p.length ∧ 1 ≤ r.length ∧
      PathFrom p a b ∧ PathFrom r a b ∧
      Disjoint (pathOccurrences p) (pathOccurrences r) ∧
      pathOccurrences p ∪ pathOccurrences r = cycleOccurrences c ∧
      pathVertices p ∩ pathVertices r = {a,b} ∧ p.length+r.length = c.length

/-- Paper `lem:pre-cycles(b)`; blueprint P1-60. -/
def S3_60Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (G : MGraph V) (c d : OccurrenceCycle G)
    (e : Occurrence G), e ∈ cycleOccurrences d → e ∉ cycleOccurrences c →
    2 ≤ (cycleVertices c ∩ cycleVertices d).card →
    ∃ (p : OccurrencePath G) (a b : V), 1 ≤ p.length ∧ a ≠ b ∧ PathFrom p a b ∧
      a ∈ cycleVertices c ∧ b ∈ cycleVertices c ∧
      pathVertices p ∩ cycleVertices c = {a,b} ∧
      pathOccurrences p ⊆ cycleOccurrences d ∧ e ∈ pathOccurrences p ∧
      Disjoint (pathOccurrences p) (cycleOccurrences c)

/-- Paper `lem:pre-cycles(b)`; blueprint P1-61. -/
def S3_61Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (K : MGraph V), Loopless K →
    (graphSupport K).Connected → ∀ c d : OccurrenceCycle K,
    Disjoint (cycleOccurrences c) (cycleOccurrences d) →
    (cycleVertices c ∩ cycleVertices d).card ≤ 1 →
    DumbbellIn K ∧
      (Disjoint (cycleVertices c) (cycleVertices d) →
        ∃ (p : OccurrencePath K) (a b : V), 1 ≤ p.length ∧ PathFrom p a b ∧
          pathVertices p ∩ cycleVertices c = {a} ∧
          pathVertices p ∩ cycleVertices d = {b} ∧
          Disjoint (pathOccurrences p) (cycleOccurrences c ∪ cycleOccurrences d))

/-- Paper `lem:pre-cycles(b)`; blueprint P1-62. -/
def S3_62Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (G : MGraph V) (c : OccurrenceCycle G)
    (p : OccurrencePath G) (a b : V), 1 ≤ p.length → a ≠ b → PathFrom p a b →
    a ∈ cycleVertices c → b ∈ cycleVertices c →
    pathVertices p ∩ cycleVertices c = {a,b} →
    Disjoint (pathOccurrences p) (cycleOccurrences c) → ThetaIn G

/-- Paper `lem:pre-cycles(b)`; blueprint P1-63a. -/
def S3_63aStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
  ∀ K : MGraph V, Loopless K → (graphSupport K).Connected →
    Fintype.card V + 1 ≤ edgeCount K → ThetaIn K ∨ DumbbellIn K

/-- Paper `lem:pre-cycles(b)`; blueprint P1-63b. -/
def S3_63bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (G : MGraph V), Loopless G →
    ThetaIn G ∨ DumbbellIn G →
    ∃ F : MGraph V, subgraph F G ∧ Loopless F ∧ (ExactTheta F ∨ ExactDumbbell F)

/-- Paper `lem:pre-cycles(b)`; blueprint P1-63. -/
def S3_63Statement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
  ∀ K : MGraph V, Loopless K → (graphSupport K).Connected →
    Fintype.card V + 1 ≤ edgeCount K →
    ∃ F : MGraph V, subgraph F K ∧ Loopless F ∧ (ExactTheta F ∨ ExactDumbbell F)

theorem S3_63_assembly (ha : S3_63aStatement.{u}) (hb : S3_63bStatement.{u}) :
    S3_63Statement.{u} := by
  intro V _ hV K hK hconn hsize
  exact hb V K hK (ha V hV K hK hconn hsize)

/-- Paper `lem:pre-cycles`; blueprint P1-64. -/
def S3_64Statement : Prop := S3_57Statement.{u} ∧ S3_63Statement.{u}
theorem S3_64_assembly (h57 : S3_57Statement.{u}) (h63 : S3_63Statement.{u}) :
    S3_64Statement.{u} := ⟨h57,h63⟩

/-- Paper `lem:pre-centre(b)`; blueprint P1-65. -/
def S3_65Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
  ∀ G : MGraph V, Loopless G → ¬ Colorable q G →
    ∃ (k : ℕ) (F : MGraph V), 2 ≤ k ∧ k ≤ Fintype.card V ∧
      subgraph F G ∧ Witness k F ∧ edgeCount F = k+1

/-- Paper `lem:pre-centre(b)`; blueprint P1-66. -/
def S3_66Statement : Prop :=
  ∀ (V : Type u) [Fintype V],
  (∀ G : MGraph V, ExactTheta G →
    let k := (vertexSupport G).card
    2 ≤ k ∧ edgeCount G = k+1 ∧
    ∃ (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
      1 ≤ j₁ ∧ 1 ≤ j₂ ∧ 1 ≤ j₃ ∧ j₁+j₂+j₃ = k+1 ∧
      G = thetaCode hk j₁ j₂ j₃ v) ∧
  (∀ (k : ℕ) (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
    2 ≤ k → 1 ≤ j₁ → 1 ≤ j₂ → 1 ≤ j₃ → j₁+j₂+j₃ = k+1 →
    ExactTheta (thetaCode hk j₁ j₂ j₃ v) ∧
      (vertexSupport (thetaCode hk j₁ j₂ j₃ v)).card = k ∧
      edgeCount (thetaCode hk j₁ j₂ j₃ v) = k+1)

/-- Paper `lem:pre-centre(b)`; blueprint P1-67. -/
def S3_67Statement : Prop :=
  ∀ (V : Type u) [Fintype V],
  (∀ G : MGraph V, ExactDumbbell G →
    let k := (vertexSupport G).card
    2 ≤ k ∧ edgeCount G = k+1 ∧
    ∃ (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
      2 ≤ j₁ ∧ 2 ≤ j₂ ∧ j₁+j₂+j₃ = k+1 ∧
      G = dumbbellCode hk j₁ j₂ j₃ v) ∧
  (∀ (k : ℕ) (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
    2 ≤ k → 2 ≤ j₁ → 2 ≤ j₂ → j₁+j₂+j₃ = k+1 →
    ExactDumbbell (dumbbellCode hk j₁ j₂ j₃ v) ∧
      (vertexSupport (dumbbellCode hk j₁ j₂ j₃ v)).card = k ∧
      edgeCount (dumbbellCode hk j₁ j₂ j₃ v) = k+1)

/-- Paper `lem:pre-centre(b)`; blueprint P1-68. -/
def S3_68Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (k : ℕ), 2 ≤ k → k ≤ Fintype.card V →
    {G : MGraph V | Witness k G}.Finite ∧
    {G : MGraph V | Witness k G}.ncard ≤ 2*(k+2)^2*(Fintype.card V)^k ∧
    ∀ G : MGraph V, Witness k G → edgeCount G = k+1

/-- Paper `lem:pre-centre(b)`; blueprint P1-69. -/
def S3_69Statement : Prop :=
  ∀ (E : Type u) [Fintype E] (p x : List E),
    ((∀ e : E, p.count e ≤ x.count e) ↔
      ∃ ι : Fin p.length ↪ Fin x.length, ∀ j, p.get j = x.get (ι j)) ∧
    Fintype.card {ι : Fin p.length ↪ Fin x.length // ∀ j, p.get j = x.get (ι j)} ≤
      x.length ^ p.length

/-- Paper `lem:pre-centre(b)`; blueprint P1-70. -/
def S3_70Statement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    ∀ (F : MGraph V) (m : ℕ), Loopless F →
    graphProb m (fun G => subgraph F G) ≤
      ((m : ℝ) / Fintype.card (Pair V)) ^ edgeCount F

/-- Paper `lem:pre-centre(b)`; blueprint P1-71. -/
def S3_71Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
    ∀ m : ℕ, 1-processSurvival (V := V) q m ≤
    ∑ k ∈ Finset.Icc 2 (Fintype.card V),
      2*((k+2 : ℕ) : ℝ)^2*(Fintype.card V : ℝ)^k *
        ((m : ℝ) / ((Fintype.card V).choose 2 : ℝ))^(k+1)

end ThLean.BP.S3

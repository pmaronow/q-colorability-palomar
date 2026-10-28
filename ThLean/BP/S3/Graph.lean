import ThLean.BP.S3.Support

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `def:pre-multigraph`; blueprint P1-01. -/
def S3_01Statement : Prop :=
  ∀ (V : Type u) (W : Type v) [Fintype V] [Fintype W] (q : ℕ), 2 ≤ q →
  (∀ (G : MGraph V) (u v : V), u ≠ v → ∀ σ : V → Fin q,
    IsColoring q (addEdge G s(u,v)) σ ↔ IsColoring q G σ ∧ σ u ≠ σ v) ∧
  (∀ G H : MGraph V, subgraph G H → colorings q H ⊆ colorings q G) ∧
  (∀ G : MGraph V, colorings q (simpleGraph (edgeSupport G)) = colorings q G) ∧
  (∀ (G : MGraph V) (π : V ≃ W) (σ : V → Fin q),
    IsColoring q (relabel π G) (σ ∘ π.symm) ↔ IsColoring q G σ) ∧
  (∀ (G : MGraph V) (π : V ≃ W) (u : V), degree (relabel π G) (π u) = degree G u) ∧
  (∀ (G : MGraph V) (e : Pair V), 0 < G e.val → addPair (erasePair G e) e = G) ∧
  Colorable q (0 : MGraph V)

/-- Paper `def:pre-process`; blueprint P1-03a. -/
def S3_03aStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    Fintype.card (Pair V) = (Fintype.card V).choose 2 ∧
    0 < Fintype.card (Pair V) ∧
    ∀ u : V, (Finset.univ.filter (fun e : Pair V => Touches u e.val)).card =
      Fintype.card V - 1

/-- Paper `def:pre-process`; blueprint P1-03b. -/
def S3_03bStatement : Prop :=
  ∀ (V : Type u) (W : Type v) [Fintype V] [Fintype W], 2 ≤ Fintype.card V →
  (∀ (m k : ℕ) (u : V),
    graphProb m (fun G => degree G u = k) = binomialWeight m (2 / Fintype.card V) k) ∧
  (∀ u : V, uniformProb (fun e : Pair V => Touches u e.val) = 2 / Fintype.card V) ∧
  (∀ (π : V ≃ W) (m : ℕ) (f : MGraph W → ℝ≥0∞),
    graphMeanENN m (fun G => f (relabel π G)) = graphMeanENN m f)

/-- Paper `def:pre-process`; blueprint P1-03. -/
def S3_03Statement : Prop := S3_03aStatement.{u} ∧ S3_03bStatement.{u, v}
theorem S3_03_assembly (ha : S3_03aStatement.{u}) (hb : S3_03bStatement.{u, v}) : S3_03Statement.{u, v} := ⟨ha,hb⟩

/-- Paper `def:pre-frozen`; blueprint P1-09a. -/
def S3_09aStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q →
  ∀ G : MGraph V, Colorable q G →
    Equivalence (Frozen q G) ∧
    (∀ u : V, u ∈ frozenClass q G u) ∧
    (∀ C ∈ frozenClasses q G, C.Nonempty) ∧
    (∀ C ∈ frozenClasses q G, ∀ D ∈ frozenClasses q G, C = D ∨ Disjoint C D) ∧
    (∀ u : V, ∃ C ∈ frozenClasses q G, u ∈ C)

/-- Paper `lem:pre-frozen(b)`; blueprint P1-09b. -/
def S3_09bStatement : Prop :=
  ∀ (V : Type u) (W : Type v) [Fintype V] [Fintype W] (q : ℕ), 2 ≤ q →
  (∀ G H : MGraph V, subgraph G H → Colorable q H →
    Colorable q G ∧ (∀ u v, Frozen q G u v → Frozen q H u v) ∧
    (∀ u, frozenClass q G u ⊆ frozenClass q H u) ∧ kappa q G ≤ kappa q H) ∧
  (∀ (G : MGraph V) (π : V ≃ W) (u : V),
    frozenClass q (relabel π G) (π u) = (frozenClass q G u).image π) ∧
  (∀ (G : MGraph V) (π : V ≃ W),
    kappa q (relabel π G) = kappa q G ∧ classMass q (relabel π G) = classMass q G) ∧
  (∀ G : MGraph V, 0 ≤ kappa q G ∧ kappa q G ≤ 1)

/-- Paper `def:pre-frozen`; blueprint P1-09. -/
def S3_09Statement : Prop := S3_09aStatement.{u} ∧ S3_09bStatement.{u, v}
theorem S3_09_assembly (ha : S3_09aStatement.{u}) (hb : S3_09bStatement.{u, v}) : S3_09Statement.{u, v} := ⟨ha,hb⟩

/-- Paper `lem:pre-frozen(a)`; blueprint P1-10. -/
def S3_10Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  (∀ (G : MGraph V) (e : Pair V),
    Colorable q (addPair G e) ↔ Colorable q G ∧ ¬ FrozenPair q G e) ∧
  (∀ G : MGraph V,
    uniformProb (fun e : Pair V => Colorable q G ∧ ¬ Colorable q (addPair G e)) = kappa q G) ∧
  (∀ (G : MGraph V) (e : Pair V), Colorable q G → 0 < G e.val → ¬ FrozenPair q G e) ∧
  (∀ (G : MGraph V) (u : V),
    (∃ e : Pair V, Touches u e.val ∧ FrozenPair q G e) ↔ inFrozenPair q G u)

/-- Paper `lem:pre-frozen(c)`; blueprint P1-11. -/
def S3_11Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  (∀ G : MGraph V, Colorable q G →
    (∑ C ∈ frozenClasses q G, C.card) = Fintype.card V ∧
    (∑ C ∈ frozenClasses q G, C.card * (C.card - 1)) =
      2 * (Finset.univ.filter (FrozenPair q G)).card ∧
    (∑ u : V, ((frozenClass q G u).card : ℝ)) = (Fintype.card V : ℝ)^2 * classMass q G) ∧
  (∀ G : MGraph V, classMass q G =
    (1 - 1 / Fintype.card V) * kappa q G + (1 / Fintype.card V) * indicator (Colorable q G))

/-- Paper `lem:pre-frozen(c),eq:pre-kappaE`; blueprint P1-12. -/
def S3_12Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  (∀ (G : MGraph V) (C : Finset V), C ∈ frozenClasses q G →
    ((C.card : ℝ) / Fintype.card V)^2 ≤ classMass q G ∧
    (C.card : ℝ) ≤ Fintype.card V * Real.sqrt (classMass q G)) ∧
  (∀ (A : MGraph V → Pair V → Prop) (G : MGraph V),
    0 ≤ kappaKind q A G ∧ kappaKind q A G ≤ kappa q G ∧
    (¬ Colorable q G → kappaKind q A G = 0)) ∧
  (∀ A : MGraph V → Pair V → Prop, kindInvariant A →
    ∀ (π : Equiv.Perm V) G, kappaKind q A (relabel π G) = kappaKind q A G)

/-- Paper `lem:pre-frozen`; blueprint P1-13. -/
def S3_13Statement : Prop := S3_09Statement.{u, v} ∧ S3_10Statement.{u} ∧ S3_11Statement.{u} ∧ S3_12Statement.{u}
theorem S3_13_assembly (h9 : S3_09Statement.{u, v}) (h10 : S3_10Statement.{u})
    (h11 : S3_11Statement.{u}) (h12 : S3_12Statement.{u}) : S3_13Statement.{u, v} := ⟨h9,h10,h11,h12⟩

end ThLean.BP.S3

import ThLean.BP.S3.Graph
import ThLean.BP.S3.Process

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `eq:pre-hazard,eq:pre-terminal-event`; blueprint P1-14. -/
def S3_14Statement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V → ∀ m : ℕ,
  (∀ (z : EdgeTuple V m → ℝ≥0∞) (F : EdgeTuple V m → Pair V → ℝ≥0∞),
    uniformMeanENN (fun x : EdgeTuple V (m+1) =>
      z (initTuple x) * F (initTuple x) (lastPair x)) =
    uniformMeanENN (fun x : EdgeTuple V m => z x * uniformMeanENN (F x))) ∧
  (∀ (z : EdgeTuple V m → ℝ) (F : EdgeTuple V m → Pair V → ℝ),
    uniformMean (fun x : EdgeTuple V (m+1) =>
      z (initTuple x) * F (initTuple x) (lastPair x)) =
    uniformMean (fun x : EdgeTuple V m => z x * uniformMean (F x)))

/-- Paper `lem:pre-hazard`; blueprint P1-15. -/
def S3_15Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  ∀ (m : ℕ) (z : EdgeTuple V m → ℝ≥0∞),
    uniformMeanENN (fun x : EdgeTuple V (m+1) => z (initTuple x) *
      if Colorable q (tupleGraph (initTuple x)) ∧ ¬ Colorable q (tupleGraph x) then 1 else 0) =
    uniformMeanENN (fun x : EdgeTuple V m =>
      z x * ENNReal.ofReal (kappa q (tupleGraph x)))

/-- Paper `lem:pre-hazard,eq:pre-hazard-sum`; blueprint P1-16. -/
def S3_16Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  ∀ (J : Set ℕ) (z : (m : ℕ) → EdgeTuple V m → ℝ),
    (∀ m ∈ J, ∀ x, 0 ≤ z m x ∧ z m x ≤ 1) →
    let a := fun m => if m ∈ J then uniformMean (fun x : EdgeTuple V m =>
      z m x * kappa q (tupleGraph x)) else 0
    Summable a ∧ (∑' m, a m) ≤ (∑' m, if m ∈ J then hittingMass (V := V) q m else 0) ∧
    (∑' m, if m ∈ J then hittingMass (V := V) q m else 0) ≤ 1 ∧
    (∑' m, hittingMass (V := V) q m) = 1 - infiniteHittingProbability (V := V) q

/-- Paper `eq:pre-terminal-event`; blueprint P1-17. -/
def S3_17Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  ∀ A : MGraph V → Pair V → Prop,
  (∀ (m : ℕ) (h : MGraph V → ℝ≥0∞),
    terminalStepENN q m (fun G e => if A G e then h G else 0) =
    graphMeanENN m (fun G => ENNReal.ofReal (kappaKind q A G) * h G)) ∧
  (AdmissibleKind q A → ∀ (ω : EdgeStream V) (m : ℕ), A (processGraph ω m) (ω m) ↔
    hittingTime q ω = ((m+1 : ℕ) : WithTop ℕ) ∧
    ∃ G e, lastGraph q ω = some G ∧ finalEdge q ω = some e ∧ A G e)

/-- Paper `lem:pre-terminal(a)`; blueprint P1-18. -/
def S3_18Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  ∀ A : MGraph V → Pair V → Prop,
  ∀ (J : Set ℕ) (h : ℕ → MGraph V → ℝ≥0∞),
    terminalSetRangeENN q J A h =
      ∑' m : ℕ, if m ∈ J then
        graphMeanENN m (fun G => ENNReal.ofReal (kappaKind q A G) * h m G) else 0

theorem S3_18_assembly (h17 : S3_17Statement.{u}) : S3_18Statement.{u} := by
  intro V _ q hq hV A J h
  unfold terminalSetRangeENN
  apply tsum_congr
  intro m
  split_ifs
  · exact (h17 V q hq hV A).1 m (h m)
  · rfl

/-- Paper `lem:pre-terminal(b)`; blueprint P1-19a. -/
def S3_19aStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (e f : Pair V),
    ∃ π : Equiv.Perm V, Sym2.map π e.val = f.val

/-- Paper `lem:pre-terminal(b)`; blueprint P1-19b. -/
def S3_19bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  ∀ (A : MGraph V → Pair V → Prop) (h : MGraph V → ℝ≥0∞)
    (ν : MGraph V → ℝ≥0∞),
    AdmissibleKind q A → kindInvariant A → RelabelInvariantENN h →
    (∀ (π : Equiv.Perm V) G, ν (relabel π G) = ν G) →
    ∀ e : Pair V,
      (∑' G, ν G * (ENNReal.ofReal (kappaKind q A G) * h G)) =
      ∑' G, ν G * (if A G e then h G else 0)

/-- Paper `lem:pre-terminal(b)`; blueprint P1-19. -/
def S3_19Statement : Prop := S3_19aStatement.{u} ∧ S3_19bStatement.{u}
theorem S3_19_assembly (ha : S3_19aStatement.{u}) (hb : S3_19bStatement.{u}) : S3_19Statement.{u} := ⟨ha,hb⟩

/-- Paper `lem:pre-hazard,lem:pre-terminal`; blueprint P1-20. -/
def S3_20Statement : Prop :=
  S3_04bStatement.{u} ∧ S3_15Statement.{u} ∧ S3_16Statement.{u} ∧ S3_18Statement.{u} ∧ S3_19Statement.{u}
theorem S3_20_assembly (h4 : S3_04bStatement.{u}) (h15 : S3_15Statement.{u})
    (h16 : S3_16Statement.{u}) (h18 : S3_18Statement.{u}) (h19 : S3_19Statement.{u}) :
    S3_20Statement.{u} := ⟨h4,h15,h16,h18,h19⟩

end ThLean.BP.S3

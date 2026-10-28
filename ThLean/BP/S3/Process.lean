import ThLean.BP.S3.Support

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `def:pre-process`; blueprint P1-02. -/
def S3_02Statement : Prop :=
  ∀ (E : Type u) [Fintype E] [Nonempty E] (M k : ℕ) (ι : Fin k ↪ Fin M),
  (∀ x : Fin k → E,
    uniformProb (fun y : Fin M → E => ∀ j, y (ι j) = x j) =
      (Fintype.card E : ℝ)^(-(k : ℤ))) ∧
  (∀ F : (Fin k → E) → ℝ≥0∞,
    uniformMeanENN (fun y : Fin M → E => F (fun j => y (ι j))) = uniformMeanENN F) ∧
  (∀ F : (Fin k → E) → ℝ,
    uniformMean (fun y : Fin M → E => F (fun j => y (ι j))) = uniformMean F) ∧
  (∀ (a b : ℕ) (i : Fin a ↪ Fin M) (j : Fin b ↪ Fin M),
    Disjoint (Set.range i) (Set.range j) →
    ∀ (f : (Fin a → E) → ℝ≥0∞) (g : (Fin b → E) → ℝ≥0∞),
    uniformMeanENN (fun y : Fin M → E =>
      f (fun r => y (i r)) * g (fun r => y (j r))) = uniformMeanENN f * uniformMeanENN g)

/-- Paper `eq:pre-H`; blueprint P1-04a. -/
def S3_04aStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q →
  (∀ (ω : EdgeStream V), (1 : WithTop ℕ) ≤ hittingTime q ω) ∧
  (∀ (ω : EdgeStream V) (m : ℕ),
    ((m : WithTop ℕ) < hittingTime q ω ↔ Colorable q (processGraph ω m)) ∧
    (hittingTime q ω = ((m+1 : ℕ) : WithTop ℕ) ↔
      Colorable q (processGraph ω m) ∧ ¬ Colorable q (processGraph ω (m+1)))) ∧
  IsStoppingTime (hittingTime (V := V) q) ∧
  Antitone (processSurvival (V := V) q)

/-- Paper `eq:pre-H,eq:pre-terminal-event`; blueprint P1-04b. -/
def S3_04bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q →
  ∀ (ω : EdgeStream V) (h : ℕ), hittingTime q ω = (h : WithTop ℕ) →
    1 ≤ h ∧ lastGraph q ω = some (processGraph ω (h-1)) ∧
    finalEdge q ω = some (ω (h-1)) ∧ Colorable q (processGraph ω (h-1)) ∧
    FrozenPair q (processGraph ω (h-1)) (ω (h-1))

/-- Paper `eq:pre-H`; blueprint P1-04. -/
def S3_04Statement : Prop := S3_04aStatement.{u} ∧ S3_04bStatement.{u}
theorem S3_04_assembly (ha : S3_04aStatement.{u}) (hb : S3_04bStatement.{u}) : S3_04Statement.{u} := ⟨ha,hb⟩

/-- Paper `eq:pre-V,eq:pre-V-H`; blueprint P1-05. -/
def S3_05Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q M : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  (∀ x : EdgeTuple V M, cappedLast q x ≤ M) ∧
  (∀ (ω : EdgeStream V) (m : ℕ),
    let x : EdgeTuple V M := fun i => ω i.val
    (m ≤ M → (m ≤ cappedLast q x ↔ (m : WithTop ℕ) < hittingTime q ω)) ∧
    (m < M → (cappedLast q x ≤ m ↔ hittingTime q ω ≤ ((m+1 : ℕ) : WithTop ℕ)))) ∧
  (∀ m ≤ M, cappedTail (V := V) q M m = processSurvival (V := V) q m) ∧
  (∀ m < M, cappedCDF (V := V) q M m = 1 - processSurvival (V := V) q (m+1)) ∧
  (∀ m, PrefixEvent (V := V) M (fun ω =>
    cappedLast q (fun i : Fin M => ω i.val) ≤ m))

/-- Paper `def:pre-quantile`; blueprint P1-06a. -/
def S3_06aStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℕ) (M : ℕ) (η : ℝ), Measurable X →
    (∀ᵐ ω ∂μ, X ω ≤ M) → 0 < η → η ≤ 1/2 →
    let L := lawLower μ X M η
    let U := lawUpper μ X M η
    L ≤ M ∧ U ≤ M ∧ η ≤ natCDF μ X L ∧ η ≤ natTail μ X U ∧
    (∀ m < L, natCDF μ X m < η) ∧
    (∀ m, U < m → m ≤ M → natTail μ X m < η) ∧
    (∀ m, η ≤ natCDF μ X m → L ≤ m)

/-- Paper `def:pre-quantile`; blueprint P1-06b. -/
def S3_06bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q M : ℕ) (η : ℝ),
    2 ≤ Fintype.card V → 0 < η → η ≤ 1/2 →
    let L := lowerQuantile (V := V) q M η
    let U := upperQuantile (V := V) q M η
    L ≤ M ∧ U ≤ M ∧ η ≤ cappedCDF (V := V) q M L ∧
    η ≤ cappedTail (V := V) q M U ∧
    (∀ m < L, cappedCDF (V := V) q M m < η) ∧
    (∀ m, U < m → m ≤ M → cappedTail (V := V) q M m < η) ∧
    (∀ m, η ≤ cappedCDF (V := V) q M m → L ≤ m)

/-- Paper `def:pre-quantile`; blueprint P1-06. -/
def S3_06Statement : Prop := S3_06aStatement.{u} ∧ S3_06bStatement.{u}
theorem S3_06_assembly (ha : S3_06aStatement.{u}) (hb : S3_06bStatement.{u}) : S3_06Statement.{u} := ⟨ha,hb⟩

/-- Paper `lem:pre-quantile`; blueprint P1-07a. -/
def S3_07aStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℕ) (M : ℕ) (η : ℝ), Measurable X →
    (∀ᵐ ω ∂μ, X ω ≤ M) → 0 < η → η ≤ 1/2 →
    1-η < natTail μ X (lawLower μ X M η) ∧
    lawLower μ X M η ≤ lawUpper μ X M η ∧
    (∀ η' : ℝ, 0 < η' → η' ≤ η →
      lawLower μ X M η' ≤ lawLower μ X M η ∧
      lawUpper μ X M η ≤ lawUpper μ X M η')

/-- Paper `lem:pre-quantile`; blueprint P1-07b. -/
def S3_07bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q M : ℕ) (η : ℝ),
    2 ≤ q → 2 ≤ Fintype.card V → 0 < η → η ≤ 1/2 →
    let L := lowerQuantile (V := V) q M η
    let U := upperQuantile (V := V) q M η
    L ≤ U ∧ U ≤ M ∧ 0 ≤ quantileWindow (V := V) q M η ∧
    (∀ m ≤ L, 1-η < processSurvival (V := V) q m) ∧
    (∀ m, U < m → m ≤ M → processSurvival (V := V) q m < η) ∧
    (∀ η' : ℝ, 0 < η' → η' ≤ η →
      lowerQuantile (V := V) q M η' ≤ L ∧ U ≤ upperQuantile (V := V) q M η')

/-- Paper `lem:pre-quantile`; blueprint P1-07. -/
def S3_07Statement : Prop := S3_07aStatement.{u} ∧ S3_07bStatement.{u}
theorem S3_07_assembly (ha : S3_07aStatement.{u}) (hb : S3_07bStatement.{u}) : S3_07Statement.{u} := ⟨ha,hb⟩

/-- Paper `lem:pre-quantile`; blueprint P1-08. -/
def S3_08Statement : Prop := S3_05Statement.{u} ∧ S3_06Statement.{u} ∧ S3_07Statement.{u}
theorem S3_08_assembly (h5 : S3_05Statement.{u}) (h6 : S3_06Statement.{u})
    (h7 : S3_07Statement.{u}) : S3_08Statement.{u} := ⟨h5,h6,h7⟩

end ThLean.BP.S3

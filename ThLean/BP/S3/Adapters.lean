import ThLean.BP.S3.Main

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `def:pre-process`; blueprint P1-02b. -/
def S3_02bStatement : Prop :=
  (∀ (A : Type u) (B : Type v) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (f : B → ℝ), uniformMean (f ∘ e) = uniformMean f) ∧
  (∀ (A : Type u) (B : Type v) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A × B → ℝ),
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))))

/-- Paper `eq:pre-kappaE`; blueprint P1-02c. -/
def S3_02cStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
  ∀ (q : ℕ) (A : MGraph V → Pair V → Prop) (G : MGraph V),
    kappaKindENN q A G = ENNReal.ofReal (kappaKind q A G)

/-- Paper `lem:pre-hazard`; blueprint P1-15b. -/
def S3_15bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  ∀ (m : ℕ) (h : MGraph V → ℝ≥0∞),
    terminalStepENN q m (fun G _ => h G) =
      graphMeanENN m (fun G => h G * ENNReal.ofReal (kappa q G))

/-- Paper `lem:pre-hazard`; blueprint P1-16b. -/
def S3_16bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
    (∀ (J : Finset ℕ) (h : ℕ → MGraph V → ℝ),
      (∀ m ∈ J, ∀ G, 0 ≤ h m G ∧ h m G ≤ 1) →
      (∑ m ∈ J, graphMean m (fun G => h m G * kappa q G)) ≤
        ∑ m ∈ J, hittingMass (V := V) q m) ∧
    (∀ J : Finset ℕ, (∑ m ∈ J, hittingMass (V := V) q m) ≤ 1)

/-- Paper `lem:pre-lifetime(a)`; blueprint P1-26b. -/
def S3_26bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2*q ≤ Fintype.card V →
  ∀ G : MGraph V,
    lifetime q G ≤ ENNReal.ofReal (lifetimeConstant q * Fintype.card V) ∧
    lifetime q G < ⊤ ∧ Summable (survival q G) ∧
    lifetimeReal q G = ∑' k : ℕ, survival q G k

/-- Paper `lem:pre-lifetime(c)`; blueprint P1-27b. -/
def S3_27bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
    ∀ G : MGraph V, 0 < kappa q G →
      lifetime q G ≤ ENNReal.ofReal (1/kappa q G)

/-- Paper `lem:pre-lifetime(d)`; blueprint P1-28b. -/
def S3_28bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  ∀ m : ℕ, graphMeanENN m (fun G : MGraph V => lifetime q G) =
    ∑' k : ℕ, ENNReal.ofReal (processSurvival (V := V) q (m+k))

/-- Paper `def:pre-multigraph,lem:pre-lifetime(b)`; blueprint P1-01b. -/
def S3_01bStatement : Prop :=
  ∀ (V : Type u) (W : Type v) [Fintype V] [Fintype W]
    (e : V ≃ W) (q : ℕ) (G : MGraph V),
    (Colorable q (relabel e G) ↔ Colorable q G) ∧
    (∀ a, degree (relabel e G) (e a) = degree G a) ∧
    (∀ a b, Frozen q (relabel e G) (e a) (e b) ↔ Frozen q G a b) ∧
    lifetime q (relabel e G) = lifetime q G ∧
    (∀ b, truncatedLifetime q b (relabel e G) = truncatedLifetime q b G) ∧
    (∀ m (h : MGraph W → ℝ), graphMean m (fun F : MGraph V => h (relabel e F)) =
      graphMean m h)

/-- Paper `lem:pre-split`; blueprint P1-36b. -/
def S3_36bStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
  ∀ (t : ℝ) (h : MGraph V → ℝ≥0∞), 0 ≤ t →
    poissonGraphMeanENN t h = independentPoissonGraphMeanENN (looplessRate t) h

/-- Paper `lem:pre-split(b)`; blueprint P1-37c. -/
def S3_37cStatement : Prop :=
  ∀ (A : Type u) (B : Type v) [Fintype A] [Fintype B],
    3 ≤ Fintype.card (A ⊕ B) → 2 ≤ Fintype.card B →
    ∀ (t : ℝ) (h : MGraph (A ⊕ B) → ℝ≥0∞), 0 ≤ t →
      poissonGraphMeanENN t h =
        poissonGraphMeanENN
          (t * ((Fintype.card A).choose 2 : ℝ) / ((Fintype.card (A ⊕ B)).choose 2 : ℝ))
          (fun GA : MGraph A => poissonGraphMeanENN
            (t * ((Fintype.card B).choose 2 : ℝ) / ((Fintype.card (A ⊕ B)).choose 2 : ℝ))
            (fun GB : MGraph B => independentPoissonListsMeanENN
              (t * Fintype.card B / ((Fintype.card (A ⊕ B)).choose 2 : ℝ))
              (fun xs : A → List B => h (splitUnionGraph GA GB xs))))

/-- Paper `lem:pre-split(c)`; blueprint P1-38c. -/
def S3_38cStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    ∀ (t : ℝ) (h : MGraph (Option V) → ℝ≥0∞), 0 ≤ t →
      poissonGraphMeanENN t h =
        poissonGraphMeanENN (((Fintype.card V : ℝ)-1)*t/((Fintype.card V : ℝ)+1))
          (fun B : MGraph V => uniformPoissonListMeanENN (2*t/((Fintype.card V : ℝ)+1))
            (fun xs => h (addRoot B xs)))

/-- Paper `lem:pre-cycles`; blueprint P1-57b. -/
def S3_57bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 3 ≤ q →
  ∀ G : MGraph V, Loopless G → ConnectedSupport G → 2 ≤ (vertexSupport G).card →
    let S := vertexSupport G
    Loopless (inducedGraph G S) ∧ (graphSupport (inducedGraph G S)).Connected ∧
    edgeCount (inducedGraph G S) = edgeCount G ∧
    (Colorable q G ↔ Colorable q (inducedGraph G S)) ∧
    (ThetaIn (inducedGraph G S) → ThetaIn G) ∧
    (DumbbellIn (inducedGraph G S) → DumbbellIn G)

/-- Paper `def:pre-process`; blueprint P1-04c. -/
def S3_04cStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    ∀ (m : ℕ) (A : Set (EdgeStream V)),
      @MeasurableSet _ (prefixSigma (V := V) m) A ↔ PrefixEvent m A

/-- Paper `def:pre-process`; blueprint P1-04d. -/
def S3_04dStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    (∀ (a : V) (j : ℕ), IsStoppingTime (degreeHittingTime a j)) ∧
    (∀ T : EdgeStream V → WithTop ℕ, IsStoppingTime T → ∀ M : ℕ,
      ∃! t : EdgeTuple V M → WithTop ℕ, IsFiniteStoppingTime t ∧
        ∀ ω : EdgeStream V, t (fun i => ω i.val) = min (T ω) M)

end ThLean.BP.S3

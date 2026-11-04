module

public import ThLean.Defs.Interface
public import ThLean.Challenge.MainDefinitions

@[expose] public section

/-! Representation obligations B00--B21 from P0. No declaration below uses
ThresholdChallenge.main; these are statements for later proof writers. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThresholdFoundations

/-- B00: the pair representations agree, and valid simple-model denominators are positive. -/
def PairBridgeStatement : Prop :=
  ∀ n : ℕ,
    (ThresholdChallenge.completeEdges n).card = n.choose 2 ∧
    Fintype.card (Pair (Fin n)) = n.choose 2 ∧
    (∃ e : ThresholdChallenge.Pair n ≃ Pair (Fin n), ∀ p, (e p).val = p.val) ∧
    ∀ m : ℕ, m ≤ n.choose 2 →
      (ThresholdChallenge.graphsWithEdges n m).card = (n.choose 2).choose m ∧
      0 < (ThresholdChallenge.graphsWithEdges n m).card

/-- B01: multiplicities, degrees, and colorability agree across representations. -/
def ColoringBridgeStatement : Prop :=
  (∀ q n m : ℕ, ∀ f : ThresholdChallenge.Pair n → Pair (Fin n),
    (∀ p, (f p).val = p.val) → ∀ x : ThresholdChallenge.EdgePrefix n m,
      Loopless (tupleGraph (f ∘ x)) ∧ edgeCount (tupleGraph (f ∘ x)) = m ∧
      (ThresholdChallenge.MultigraphColorable q (ThresholdChallenge.prefixMultigraph x) ↔
        Colorable q (tupleGraph (f ∘ x))) ∧
      (∀ a : Fin n, degree (tupleGraph (f ∘ x)) a =
        ∑ i : Fin m, if Touches a (x i).val then 1 else 0)) ∧
  (∀ q n : ℕ, ∀ E : Finset (Sym2 (Fin n)), E ⊆ ThresholdChallenge.completeEdges n →
    (ThresholdChallenge.Colorable q n E ↔ Colorable q (simpleGraph E)))

/-- B02: all public finite probabilities agree with the internal laws. -/
def PublicModelsStatement : Prop :=
  (∀ q n m : ℕ, ThresholdChallenge.processSurvival q n m =
    processSurvival (V := Fin n) q m) ∧
  (∀ q n m : ℕ, ThresholdChallenge.uniformColorabilityProbability q n m =
    simpleProbability (V := Fin n) q m) ∧
  (∀ q n : ℕ, ∀ p : ℝ, ThresholdChallenge.binomialColorabilityProbability q n p =
    bernoulliProbability (V := Fin n) q p) ∧
  (∀ q n : ℕ, ∀ d : ℝ, ThresholdChallenge.sparseBinomialProbability q n d =
    sparseProbability q n d) ∧
  (∀ q : ℕ, ThresholdChallenge.gamma q = gamma q) ∧
  (∀ q n : ℕ, ∀ d : ℝ, 0 < n → 0 ≤ d → d ≤ n →
    0 ≤ sparseProbability q n d ∧ sparseProbability q n d ≤ 1)

/-- B03: projectivity, decreasing survival, and the initial value. -/
def ProjectiveConsistencyStatement : Prop :=
  PreFiniteLawsStatement.{0, 0} ∧
  (∀ q n : ℕ, 1 ≤ q → 2 ≤ n →
    Antitone (processSurvival (V := Fin n) q) ∧ processSurvival (V := Fin n) q 0 = 1)

/-- B04: remove one occurrence at a specified coordinate, then average. -/
def DeletionExchangeabilityStatement : Prop :=
  ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → ∀ i : Fin m,
    ∀ f : MGraph (Fin n) → Pair (Fin n) → ℝ,
      uniformMean (fun x : EdgeTuple (Fin n) m => f (erasePair (tupleGraph x) (x i)) (x i)) =
        graphMean (m-1) (fun G => uniformMean (fun e => f G e))

/-- B05: shared hazard and terminal contracts. -/
def HazardTerminalBridgeStatement : Prop :=
  PreFrozenStatement.{0} ∧ PreHazardStatement ∧ PreTerminalStatement.{0}

/-- B06: finite lifetime and legitimate conversion from extended values. -/
def LifetimeRealBridgeStatement : Prop :=
  PreLifetimeStatement.{0} ∧ PreClassmassStatement.{0} ∧
  (∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ G : MGraph (Fin n), Loopless G →
    ENNReal.ofReal (lifetimeReal q G) = lifetime q G ∧
    (∀ y : ℝ, 0 ≤ y → (ENNReal.ofReal y < lifetime q G ↔ y < lifetimeReal q G)) ∧
    (∀ a : ℝ, 0 ≤ a →
      (min (ENNReal.ofReal a) (lifetime q G)).toReal = min a (lifetimeReal q G)))

/-- B07: the finite hitting masses and possible atom at infinity have total mass one. -/
def HittingLawStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2 ≤ n →
    (∀ k : ℕ, 0 ≤ hittingMass (V := Fin n) q k) ∧
    (0 ≤ infiniteHittingProbability (V := Fin n) q ∧
      infiniteHittingProbability (V := Fin n) q ≤ 1) ∧
    ((∑' k : ℕ, ENNReal.ofReal (hittingMass (V := Fin n) q k)) +
      ENNReal.ofReal (infiniteHittingProbability (V := Fin n) q) = 1) ∧
    (∀ m : ℕ, ENNReal.ofReal (processSurvival (V := Fin n) q m) =
      ENNReal.ofReal (infiniteHittingProbability (V := Fin n) q) +
        ∑' k : ℕ, ENNReal.ofReal (hittingMass (V := Fin n) q (m+k))) ∧
    (2*q ≤ n → infiniteHittingProbability (V := Fin n) q = 0)

/-- B08: the real interval is rounded after adding its center. -/
def WindowProbabilityStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2 ≤ n → ∀ (a : ℤ) (w : ℝ),
    ThresholdChallenge.hittingWindowProbability q n a w =
      hittingWindowProbability (V := Fin n) q a w ∧
    (let A : ℤ := max 1 (Int.ceil ((a : ℝ)-w))
     let B : ℤ := Int.floor ((a : ℝ)+w)
     hittingWindowProbability (V := Fin n) q a w =
       if A ≤ B then processSurvival (V := Fin n) q (A-1).toNat -
         processSurvival (V := Fin n) q B.toNat else 0)

/-- B09: the cylinder filtration and its finite stopping reduction. -/
def StoppingBridgeStatement : Prop := PreStoppingStatement.{0}

/-- B10: min(H-1,M), including the infinity branch, and the quantile laws. -/
def CapQuantileBridgeStatement : Prop :=
  PreQuantileStatement ∧
  (∀ q n M : ℕ, 3 ≤ q → 2 ≤ n → ∀ ω : EdgeStream (Fin n),
    cappedLast q (fun i : Fin M => ω i.val) = cappedTime (hittingTime q ω) M)

/-- B11: clipping, omission, the deletion identity, and finite Efron--Stein. -/
def DeletionVarianceBridgeStatement : Prop :=
  (∀ q n L U M : ℕ, 3 ≤ q → 2 ≤ n → L ≤ U → ∀ hUM : U ≤ M,
    ∀ x : EdgeTuple (Fin n) M,
      deletionY q L (restrictTuple hUM x) = clippedLast q L U x) ∧
  (∀ q n L U : ℕ, ∀ i : Fin U, ∀ x y : EdgeTuple (Fin n) U,
    (∀ j : Fin U, j ≠ i → x j = y j) →
      deletionYMinus q L i x = deletionYMinus q L i y) ∧
  (∀ q n L U : ℕ, 3 ≤ q → 2 ≤ n → L ≤ U →
    (∑ i : Fin U, uniformMean (fun x : EdgeTuple (Fin n) U =>
      ((deletionYMinus q L i x : ℝ) - (deletionY q L x : ℝ))^2)) =
      terminalWindow (V := Fin n) q L U (fun m G _ =>
        ((m+1 : ℕ) : ℝ) * (2*truncatedLifetime q (U-m) G - 1))) ∧
  (∀ (A : Type) [Fintype A] [Nonempty A] (U : ℕ)
      (f : (Fin U → A) → ℝ) (g : Fin U → (Fin U → A) → ℝ),
    (∀ i x y, (∀ j, j ≠ i → x j = y j) → g i x = g i y) →
      variance f ≤ ∑ i : Fin U, uniformMean (fun x => (f x-g i x)^2))

/-- B12: quotient colorings are precisely colorings constant on the identified set. -/
def IdentificationColoringStatement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V], ∀ q : ℕ, 3 ≤ q →
    ∀ (B : MGraph V) (Z : Finset V), Loopless B → Z.Nonempty →
      (∃ e : {τ // IsColoring q (identify B Z) τ} ≃
        {σ // IsColoring q B σ ∧ constantOn σ Z},
        ∀ τ v, (e τ).val v = τ.val (identifyVertex Z v)) ∧
      Fintype.card (QuotientVertices Z) = Fintype.card V - Z.card + 1 ∧
      (∀ u ∈ Z, ∀ v ∈ Z, 0 < B s(u,v) → ¬ Colorable q (identify B Z)) ∧
      (∀ (xs : List V) (τ : Option V → Fin q),
        IsColoring q (addRoot B xs) τ ↔
          IsColoring q B (fun v => τ (some v)) ∧ ∀ v ∈ xs, τ none ≠ τ (some v))

/-- B13: uniform completion, never-monochromatic lists, and identification advance. -/
def IdentificationAdvanceStatement : Prop :=
  ∀ (V : Type) [Fintype V], ∀ q : ℕ, 3 ≤ q → 2*q ≤ Fintype.card V →
    (∀ B : MGraph V, Loopless B → Colorable q B →
      (∀ D : ℕ, D ≤ Fintype.card V →
        nmProbability q D B ≤ identificationFailureProbability q D B) ∧
      nmProbability q 0 B = 0 ∧
      (∀ D : ℕ, nmProbability q D B ≤ nmProbability q (D+1) B)) ∧
    (∀ D : ℕ, 1 ≤ D → D ≤ Fintype.card V →
      identificationAdvance (V := V) q D ≤
        ENNReal.ofReal (lifetimeConstant q * Fintype.card V))

/-- B14: normalized kernels and nonnegative occupation. -/
def PoissonOccupationStatement : Prop := PrePoissonStatement.{0}
/-- B15: independent labeled lists and graph restrictions. -/
def PoissonSplittingStatement : Prop := PreSplitStatement.{0, 0}

/-- B16: histogram laws, retaining diagonal counts in model A. -/
def PoissonHistogramStatement : Prop :=
  (∀ (V : Type) [Fintype V], 2 ≤ Fintype.card V →
    ∀ (t : ℝ) (h : MGraph V → ℝ≥0∞), 0 ≤ t →
      poissonGraphMeanENN t h = independentPoissonGraphMeanENN (looplessRate t) h) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ (c : ℝ) (h : MGraph (Fin n) → ℝ≥0∞), 0 ≤ c →
    poissonMixtureENN (c*n) (fun m =>
      uniformMeanENN (fun x : Fin m → Fin n × Fin n => h (orderedTupleGraph x))) =
        independentPoissonGraphMeanENN (poissonARate n c) h)

/-- B17: the exp(-c) factor from excluding every loop. -/
def RhoProcessStatement : Prop :=
  (∀ q n : ℕ, 3 ≤ q → 2 ≤ n → ∀ c : ℝ, 0 ≤ c →
    rho q n c = Real.exp (-c) *
      poissonMixture (c*((n : ℝ)-1)) (processSurvival (V := Fin n) q)) ∧
  (∀ q : ℕ, 3 ≤ q → ∀ c : ℝ, 0 ≤ c → rho q 1 c = Real.exp (-c))

/-- B18: smooth convergent extension and the exact frozen-class derivative. -/
def InterpolationBridgeStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 3 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ →
    (∀ k : Fin 3 → ℕ, 0 ≤ interpolationCoefficient q n₁ n₂ k ∧
      interpolationCoefficient q n₁ n₂ k ≤ 1) ∧
    (∀ μ : Fin 3 → ℝ, Summable (fun k : Fin 3 → ℕ =>
      (∏ i : Fin 3, poissonWeight (μ i) (k i)) * interpolationCoefficient q n₁ n₂ k)) ∧
    (∀ r : ℕ,
      (∀ μ : Fin 3 → ℝ, Summable (fun k : Fin 3 → ℕ =>
        ‖iteratedFDeriv ℝ r (interpolationTerm q n₁ n₂ k) μ‖)) ∧
      TendstoLocallyUniformly (interpolationDerivativeNormPartial q n₁ n₂ r)
        (fun μ => ∑' k : Fin 3 → ℕ, ‖iteratedFDeriv ℝ r (interpolationTerm q n₁ n₂ k) μ‖)
        atTop) ∧
    (∀ r : ℕ, ContDiff ℝ r (chiBar q n₁ n₂)) ∧
    (∀ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) → chiBar q n₁ n₂ μ = chiSupport q n₁ n₂ μ) ∧
    (∀ c θ : ℝ, 0 < c → 0 < θ → θ < c →
      HasDerivAt (chi q n₁ n₂ c)
        (poissonInterpolationMean n₁ n₂ (interpolationMeans n₁ n₂ c θ)
          (interpolationClassDrift q n₁ n₂)) θ ∧
      0 ≤ poissonInterpolationMean n₁ n₂ (interpolationMeans n₁ n₂ c θ)
        (interpolationClassDrift q n₁ n₂)) ∧
    (∀ c : ℝ, 0 ≤ c →
      chi q n₁ n₂ c 0 = rho q n₁ c * rho q n₂ c ∧
      chi q n₁ n₂ c c = rho q (n₁+n₂) c ∧
      rho q n₁ c * rho q n₂ c ≤ rho q (n₁+n₂) c)

/-- B19: no-repeat conditioning is expressed as a joint probability identity. -/
def DistinctTransferStatement : Prop :=
  (∀ q n m : ℕ, 3 ≤ q → 2 ≤ n → m ≤ n.choose 2 →
    uniformProb (fun x : EdgeTuple (Fin n) m =>
      DistinctPrefix x ∧ Colorable q (tupleGraph x)) =
      uniformProb (fun x : EdgeTuple (Fin n) m => DistinctPrefix x) *
        simpleProbability (V := Fin n) q m) ∧
  (∀ n m : ℕ, 2 ≤ n → m ≤ n.choose 2 →
    uniformProb (fun x : EdgeTuple (Fin n) m => DistinctPrefix x) =
      ∏ i ∈ Finset.range m, (1 - (i : ℝ)/(n.choose 2 : ℝ)) ∧
    0 < uniformProb (fun x : EdgeTuple (Fin n) m => DistinctPrefix x)) ∧
  (∀ Λ : ℝ, 0 < Λ → ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ Λ*n →
    Real.exp (-2*Λ^2-1) ≤ uniformProb (fun x : EdgeTuple (Fin n) m => DistinctPrefix x))
/-- B20: binomial mixing and both comparison inequalities. -/
def BinomialTransferStatement : Prop := ConvTransferStatement
/-- B21: valid eventual domains and uniqueness of the process threshold. -/
def EventualDomainStatement : Prop :=
  (∀ c : ℝ, 0 ≤ c → ∀ᶠ n : ℕ in atTop,
    Nat.floor (c*n) ≤ n.choose 2 ∧ (Nat.floor (c*n) : ℤ) = Int.floor (c*n)) ∧
  (∀ d : ℝ, 0 ≤ d → ∀ᶠ n : ℕ in atTop, 0 < n ∧ d ≤ (n : ℝ)) ∧
  (∀ (q : ℕ) (α β : ℝ), 3 ≤ q → α ∈ Set.Icc (1/2 : ℝ) (gamma q) →
    β ∈ Set.Icc (1/2 : ℝ) (gamma q) → ProcessLimits q α → ProcessLimits q β → α = β)

/-- The precise shared inputs to the final assembly. LowMain feeds CorLow within
Section 5; the deletion/variance results feed RedSplit within Section 4; the
interpolation/tree/transfer lemmas feed RedConvergence within Appendix A. -/
def MainFromSections : Prop :=
  PreQuantileStatement → PreCentreStatement → RedSplitStatement →
    CorLowStatement → HighMainStatement → EpsilonAdmissibleStatement →
    RedConvergenceStatement → PublicModelsStatement → WindowProbabilityStatement →
    ThresholdChallenge.MainStatement
end ThresholdFoundations

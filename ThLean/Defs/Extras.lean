module

public import ThLean.Defs.Low
public import ThLean.Defs.Cycles
public import ThLean.Defs.Poisson
public import ThLean.Defs.Parameters
public import ThLean.Defs.Tree

@[expose] public section

/-! Additional concrete objects required by the five section blueprints. -/
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThresholdFoundations

section Finite
variable {V : Type*} [Fintype V]

/-- Expectation under the length-m uniform edge law. -/
def graphMean (m : ℕ) (h : MGraph V → ℝ) : ℝ :=
  uniformMean (fun x : EdgeTuple V m => h (tupleGraph x))
def graphMeanENN (m : ℕ) (h : MGraph V → ℝ≥0∞) : ℝ≥0∞ :=
  uniformMeanENN (fun x : EdgeTuple V m => h (tupleGraph x))
def restrictTuple {r m : ℕ} (hrm : r ≤ m) (x : EdgeTuple V m) : EdgeTuple V r :=
  fun i => x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hrm⟩

/-- Terminal cylinder at H=m+1, allowing signed finite test functions. -/
def terminalStep (q m : ℕ) (h : MGraph V → Pair V → ℝ) : ℝ :=
  uniformMean (fun x : EdgeTuple V m => uniformMean (fun e : Pair V =>
    if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
    then h (tupleGraph x) e else 0))
/-- The time argument of h is H-1. -/
def terminalWindow (q L U : ℕ) (h : ℕ → MGraph V → Pair V → ℝ) : ℝ :=
  ∑ m ∈ Finset.Ico L U, terminalStep q m (h m)
def terminalWindowProbability (q L U : ℕ) (A : MGraph V → Pair V → Prop) : ℝ :=
  terminalWindow q L U (fun _ G e => indicator (A G e))
def terminalMeanTimeENN (q : ℕ) (h : ℕ → MGraph V → Pair V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' m : ℕ, terminalStepENN q m (h m)
def terminalRangeENN (q L : ℕ) (U : WithTop ℕ)
    (h : ℕ → MGraph V → Pair V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' m : ℕ, if L ≤ m ∧ (m : WithTop ℕ) < U then terminalStepENN q m (h m) else 0

def kappaKindENN (q : ℕ) (A : MGraph V → Pair V → Prop) (G : MGraph V) : ℝ≥0∞ :=
  uniformMeanENN (fun e : Pair V => if FrozenPair q G e ∧ A G e then 1 else 0)
def frozenPartnerCount (q : ℕ) (G : MGraph V) (u : V) : ℕ :=
  (Finset.univ.filter (fun v => v ≠ u ∧ Frozen q G u v)).card
def withoutVertex (G : MGraph V) (a : V) : MGraph {v : V // v ≠ a} :=
  fun e => G (Sym2.map Subtype.val e)
def completionKernel (D : ℕ) (xs : List V) (Z : Finset V) : ℝ :=
  if xs.toFinset ⊆ Z ∧ Z.card = D
  then 1 / ((Fintype.card V - xs.toFinset.card).choose (D - xs.toFinset.card) : ℝ)
  else 0
/-- Auxiliary stopped potential; frozen classes themselves remain empty after failure. -/
def saturatedPotential (q : ℕ) (G : MGraph V) (u : V) : ℝ :=
  if Colorable q G then potential q G u else Real.log (Fintype.card V : ℝ)
def lowWindowProbability (q L U D : ℕ) (y : ℝ) : ℝ :=
  terminalWindowProbability (V := V) q L U
    (fun G e => lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G)
def highWindowProbability (q L U D : ℕ) : ℝ :=
  terminalWindowProbability (V := V) q L U (fun G e => bothHigh G D e)
def highLongWindowProbability (q L U D : ℕ) (y : ℝ) : ℝ :=
  terminalWindowProbability (V := V) q L U
    (fun G e => bothHigh G D e ∧ ENNReal.ofReal y < lifetime q G)
/-- Use after the finite-lifetime theorem: E[min(a,r(Γ)); L<H≤U]. -/
def truncatedTerminalLifetime (q L U : ℕ) (a : ℝ) : ℝ :=
  terminalWindow (V := V) q L U (fun _ G _ => min a (lifetimeReal q G))
def looplessRate (t : ℝ) (e : Sym2 V) : ℝ :=
  if e ∈ completeEdges (V := V) then t / (Fintype.card (Pair V) : ℝ) else 0
def independentPoissonGraphMeanENN (rate : Sym2 V → ℝ)
    (h : MGraph V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' G : MGraph V, ENNReal.ofReal (independentPoissonGraphMass rate G) * h G
def graphLawMeanENN (w : MGraph V → ℝ≥0∞) (h : MGraph V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' G : MGraph V, w G * h G
def RelabelLawInvariant (w : MGraph V → ℝ≥0∞) : Prop :=
  ∀ (π : Equiv.Perm V) G, w (relabel π G) = w G
def WitnessFamily (k : ℕ) : Set (MGraph V) :=
  {G | Loopless G ∧ (vertexSupport G).card = k ∧ edgeCount G = k + 1 ∧
    (ThetaIn G ∨ DumbbellIn G)}

/-- M+1 is a sentinel for no failure among the supplied edges. -/
def finiteHittingTime {M : ℕ} (q : ℕ) (x : EdgeTuple V M) : ℕ :=
  if h : ∃ m : ℕ, m ≤ M ∧ ¬ Colorable q (tuplePrefix x m) then Nat.find h else M+1
def finiteTerminalGraph {M : ℕ} (q : ℕ) (x : EdgeTuple V M) : MGraph V :=
  tuplePrefix x (finiteHittingTime q x - 1)
def finiteStoppedTime {M : ℕ} (q : ℕ) (x : EdgeTuple V M) : ℕ :=
  min (finiteHittingTime q x) M
def finiteHighEvent {M : ℕ} (q D : ℕ) (x : EdgeTuple V M) : Prop :=
  ∃ i : Fin M, Colorable q (tuplePrefix x i.val) ∧
    ¬ Colorable q (tuplePrefix x (i.val+1)) ∧ highEdge (tuplePrefix x i.val) D (x i)
def blockingIncrementProbability (q j : ℕ) (B : MGraph V) : ℝ :=
  uniformMean (fun x : Fin j → V => uniformProb (fun v : V =>
    Colorable q (addRoot B (List.ofFn x)) ∧
    ¬ Colorable q (addRoot B (List.ofFn x ++ [v]))))
def blockingFailureProbability (q j : ℕ) (B : MGraph V) : ℝ :=
  uniformProb (fun x : Fin j → V =>
    Colorable q B ∧ ¬ Colorable q (addRoot B (List.ofFn x)))
end Finite

def cappedTime (H : WithTop ℕ) (M : ℕ) : ℕ :=
  if h : ∃ k : ℕ, H = (k : WithTop ℕ) then min (Nat.find h - 1) M else M
def entropy (x : ℝ) : ℝ := (1 + x) * Real.log (1 + x) - x
/-- Used for 0<c<1/2, after proving summability. -/
def subcriticalConstant (c : ℝ) : ℝ :=
  4 * Real.exp 2 * ∑' k : ℕ, if 2 ≤ k then ((k + 2 : ℕ) : ℝ)^2 * (2*c)^(k+1) else 0
def binomialTail (m : ℕ) (p : ℝ) (a : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), if a ≤ (k : ℝ) then binomialWeight m p k else 0
def poissonTailENN (z a : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, if a ≤ (k : ℝ) then ENNReal.ofReal (poissonWeight z k) else 0
def poissonLowerTailENN (z a : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, if (k : ℝ) ≤ a then ENNReal.ofReal (poissonWeight z k) else 0
def poissonTail (z a : ℝ) : ℝ := (poissonTailENN z a).toReal
def poissonLowerTail (z a : ℝ) : ℝ := (poissonLowerTailENN z a).toReal

def uniformPoissonListMeanENN {E : Type*} [Fintype E]
    (z : ℝ) (h : List E → ℝ≥0∞) : ℝ≥0∞ :=
  poissonMixtureENN z (fun k => uniformMeanENN (fun x : Fin k → E => h (List.ofFn x)))
def independentPoissonListsMeanENN {A B : Type*} [Fintype A] [Fintype B]
    (z : ℝ) (h : (A → List B) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' k : A → ℕ, (∏ a, ENNReal.ofReal (poissonWeight z (k a))) *
    uniformMeanENN (fun x : (a : A) → Fin (k a) → B => h (fun a => List.ofFn (x a)))
def splitUnionGraph {A B : Type*} [Fintype A] [Fintype B]
    (GA : MGraph A) (GB : MGraph B) (xs : A → List B) : MGraph (A ⊕ B) :=
  mapGraph Sum.inl GA + mapGraph Sum.inr GB +
    (fun e => ∑ a, ((xs a).map (fun b => s(Sum.inl a, Sum.inr b))).count e)

/-- Finite algebraic support weights, also defined for signed rates. -/
def poissonSupportWeight {D : Type*} [Fintype D] (rates : D → ℝ) (T : Finset D) : ℝ :=
  (∏ e ∈ T, (1 - Real.exp (-rates e))) * ∏ e ∈ Finset.univ \ T, Real.exp (-rates e)
def poissonSupportMean {D : Type*} [Fintype D]
    (rates : D → ℝ) (F : Finset D → ℝ) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset D).powerset, poissonSupportWeight rates T * F T
def supportGraph {D V : Type*} [Fintype D] (edge : D → Sym2 V) (T : Finset D) : MGraph V :=
  fun e => (T.filter (fun d => edge d = e)).card
abbrev InterpolationMark (n₁ n₂ : ℕ) :=
  (Fin (n₁+n₂) × Fin (n₁+n₂)) ⊕ ((Fin n₁ × Fin n₁) ⊕ (Fin n₂ × Fin n₂))
def interpolationMarkEdge {n₁ n₂ : ℕ} : InterpolationMark n₁ n₂ → Sym2 (Fin (n₁+n₂))
  | .inl (u,v) => s(u,v)
  | .inr (.inl (u,v)) => s(leftVertex n₁ n₂ u, leftVertex n₁ n₂ v)
  | .inr (.inr (u,v)) => s(rightVertex n₁ n₂ u, rightVertex n₁ n₂ v)
def interpolationMarkRate {n₁ n₂ : ℕ} (μ : Fin 3 → ℝ) : InterpolationMark n₁ n₂ → ℝ
  | .inl _ => μ 0 / ((n₁+n₂ : ℕ) : ℝ)^2
  | .inr (.inl _) => μ 1 / (n₁ : ℝ)^2
  | .inr (.inr _) => μ 2 / (n₂ : ℝ)^2
def chiSupport (q n₁ n₂ : ℕ) (μ : Fin 3 → ℝ) : ℝ :=
  poissonSupportMean (interpolationMarkRate (n₁ := n₁) (n₂ := n₂) μ)
    (fun T => indicator (Colorable q (supportGraph interpolationMarkEdge T)))
def interpolationClassDrift (q n₁ n₂ : ℕ) (G : MGraph (Fin (n₁+n₂))) : ℝ :=
  ∑ C ∈ frozenClasses q G,
    (((C.filter (fun v => v.val < n₁)).card : ℝ)^2 / n₁ +
      ((C.filter (fun v => n₁ ≤ v.val)).card : ℝ)^2 / n₂ -
      (C.card : ℝ)^2 / (n₁+n₂ : ℕ))
def mixedGraphMean (n₁ n₂ : ℕ) (k : Fin 3 → ℕ)
    (h : MGraph (Fin (n₁+n₂)) → ℝ) : ℝ :=
  uniformMean (fun x₀ : Fin (k 0) → Fin (n₁+n₂) × Fin (n₁+n₂) =>
    uniformMean (fun x₁ : Fin (k 1) → Fin n₁ × Fin n₁ =>
      uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ => h (mixedGraph x₀ x₁ x₂))))
def poissonInterpolationMean (n₁ n₂ : ℕ) (μ : Fin 3 → ℝ)
    (h : MGraph (Fin (n₁+n₂)) → ℝ) : ℝ :=
  ∑' k : Fin 3 → ℕ, (∏ i : Fin 3, poissonWeight (μ i) (k i)) * mixedGraphMean n₁ n₂ k h

/-- One signed-mean factorial-series summand of the interpolation. -/
def interpolationTerm (q n₁ n₂ : ℕ) (k : Fin 3 → ℕ) (μ : Fin 3 → ℝ) : ℝ :=
  (∏ i : Fin 3, poissonWeight (μ i) (k i)) * interpolationCoefficient q n₁ n₂ k
/-- Rectangular partial sum of norms of derivatives, for the B18 convergence contract. -/
def interpolationDerivativeNormPartial (q n₁ n₂ r N : ℕ) (μ : Fin 3 → ℝ) : ℝ :=
  ∑ k : Fin 3 → Fin N,
    ‖iteratedFDeriv ℝ r (interpolationTerm q n₁ n₂ (fun i => (k i).val)) μ‖

def relationNeighbors {W : Type*} [Fintype W] (R : Finset (W × W)) (a : W) : Finset W :=
  Finset.univ.filter (fun b => (a,b) ∈ R)
def relationCommon {W : Type*} [Fintype W] (R : Finset (W × W)) (a b : W) : Finset W :=
  relationNeighbors R a ∩ relationNeighbors R b
def cappedCommonSum {W : Type*} [Fintype W] (R : Finset (W × W)) (c : ℕ) : ℝ :=
  ∑ a : W, ∑ b : W, min (((relationCommon R a b).card : ℝ) / c) 1
def cappedDegreeSum {W : Type*} [Fintype W] (R : Finset (W × W)) (c : ℕ) : ℝ :=
  ∑ a : W, min (((relationNeighbors R a).card : ℝ) / c) 1

def QuantileLimits (q : ℕ) (Λ α : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ etaZero Λ →
    Tendsto (fun n : ℕ => (lowerLocation q Λ η n : ℝ) / n) atTop (𝓝 α) ∧
    Tendsto (fun n : ℕ => (upperLocation q Λ η n : ℝ) / n) atTop (𝓝 α)
def ProcessLimits (q : ℕ) (α : ℝ) : Prop :=
  (∀ c : ℝ, 0 ≤ c → c < α →
    Tendsto (fun n : ℕ => processSurvival (V := Fin n) q (Nat.floor (c*n))) atTop (𝓝 1)) ∧
  (∀ c : ℝ, α < c →
    Tendsto (fun n : ℕ => processSurvival (V := Fin n) q (Nat.floor (c*n))) atTop (𝓝 0))
def SimpleLimits (q : ℕ) (α : ℝ) : Prop :=
  (∀ c : ℝ, 0 ≤ c → c < α →
    Tendsto (fun n : ℕ => simpleProbability (V := Fin n) q (Nat.floor (c*n))) atTop (𝓝 1)) ∧
  (∀ c : ℝ, α < c →
    Tendsto (fun n : ℕ => simpleProbability (V := Fin n) q (Nat.floor (c*n))) atTop (𝓝 0))
def sparseProbability (q n : ℕ) (d : ℝ) : ℝ :=
  if 0 < n ∧ 0 ≤ d ∧ d ≤ (n : ℝ) then bernoulliProbability (V := Fin n) q (d/n) else 0
def BinomialLimits (q : ℕ) (α : ℝ) : Prop :=
  (∀ d : ℝ, 0 ≤ d → d < 2*α →
    Tendsto (fun n : ℕ => sparseProbability q n d) atTop (𝓝 1)) ∧
  (∀ d : ℝ, 2*α < d →
    Tendsto (fun n : ℕ => sparseProbability q n d) atTop (𝓝 0))
def WindowBound (q : ℕ) (Λ : ℝ) (δ : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ etaZero Λ → ∃ K : ℝ, 0 < K ∧
    ∃ N : ℕ, 2*q ≤ N ∧ ∀ n : ℕ, N ≤ n → window q Λ η n ≤ K*n*δ n
def ComparisonHypotheses (ξ : ℕ → ℝ) (g : ℝ → ℝ) (s₀ : ℕ) : Prop :=
  1 ≤ s₀ ∧
  (∀ a b : ℕ, s₀ ≤ a → s₀ ≤ b → ξ (a+b) ≥ min (ξ a) (ξ b) - g (min a b)) ∧
  (∀ a : ℕ, s₀ ≤ a → ξ (a+1) ≥ ξ a - g a)

namespace BlockTree
def leafWeights : BlockTree → List ℕ
  | .leaf n => [n]
  | .node a b => leafWeights a ++ leafWeights b
end BlockTree
end ThresholdFoundations

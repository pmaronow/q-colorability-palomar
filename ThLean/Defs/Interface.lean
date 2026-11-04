module

public import ThLean.Defs.Extras

@[expose] public section

/-! Section-level propositions used by the final theorem assembly. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThresholdFoundations

/-- Section 3 finite reindexing, Fubini, and prefix consistency. -/
def PreFiniteLawsStatement : Prop :=
  (∀ (A : Type u) (B : Type v) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
      (e : A ≃ B) (f : B → ℝ), uniformMean (f ∘ e) = uniformMean f) ∧
  (∀ (A : Type u) (B : Type v) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
      (f : A × B → ℝ),
      uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b)))) ∧
  (∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    ∀ r m : ℕ, ∀ h : r ≤ m, ∀ f : EdgeTuple V r → ℝ,
      uniformMean (fun x : EdgeTuple V m => f (restrictTuple h x)) = uniformMean f) ∧
  (∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    ∀ r m : ℕ, ∀ h : r ≤ m, ∀ f : EdgeTuple V r → ℝ≥0∞,
      uniformMeanENN (fun x : EdgeTuple V m => f (restrictTuple h x)) = uniformMeanENN f)

/-- lem:pre-frozen(a)--(c), with separate colorability guards. -/
def PreFrozenStatement : Prop :=
  ∀ (V : Type u) [Fintype V], ∀ q : ℕ, 3 ≤ q → 2 ≤ Fintype.card V →
    (∀ (G : MGraph V) (e : Pair V),
      (Colorable q (addPair G e) ↔ Colorable q G ∧ ¬ FrozenPair q G e)) ∧
    (∀ G : MGraph V,
      uniformProb (fun e : Pair V => Colorable q G ∧ ¬ Colorable q (addPair G e)) =
        kappa q G) ∧
    (∀ G G' : MGraph V, subgraph G G' → Colorable q G' →
      Colorable q G ∧ (∀ a b, Frozen q G a b → Frozen q G' a b) ∧
      (∀ a, frozenClass q G a ⊆ frozenClass q G' a) ∧ kappa q G ≤ kappa q G') ∧
    (∀ G : MGraph V, Colorable q G →
      classMass q G = (1 - 1 / (Fintype.card V : ℝ)) * kappa q G +
        1 / (Fintype.card V : ℝ)) ∧
    (∀ G : MGraph V, Colorable q G → ∀ C ∈ frozenClasses q G,
      (C.card : ℝ) ≤ (Fintype.card V : ℝ) * Real.sqrt (classMass q G))

/-- lem:pre-hazard, expressed by averaging the independent next edge. -/
def PreHazardStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2 ≤ n →
    (∀ m : ℕ, ∀ h : MGraph (Fin n) → ℝ≥0∞,
      terminalStepENN q m (fun G _ => h G) =
        graphMeanENN m (fun G => h G * ENNReal.ofReal (kappa q G))) ∧
    (∀ (J : Finset ℕ) (h : ℕ → MGraph (Fin n) → ℝ),
      (∀ m ∈ J, ∀ G, 0 ≤ h m G ∧ h m G ≤ 1) →
      (∑ m ∈ J, graphMean m (fun G => h m G * kappa q G)) ≤
        ∑ m ∈ J, hittingMass (V := Fin n) q m) ∧
    (∀ J : Finset ℕ, (∑ m ∈ J, hittingMass (V := Fin n) q m) ≤ 1)

/-- lem:pre-terminal(a),(b), for time-dependent weights and invariant discrete laws. -/
def PreTerminalStatement : Prop :=
  (∀ q n : ℕ, 3 ≤ q → 2 ≤ n →
    ∀ (A : MGraph (Fin n) → Pair (Fin n) → Prop)
      (h : ℕ → MGraph (Fin n) → ℝ≥0∞) (L : ℕ) (U : WithTop ℕ),
      terminalRangeENN q L U (fun m G e => if A G e then h m G else 0) =
        ∑' m : ℕ, if L ≤ m ∧ (m : WithTop ℕ) < U then
          graphMeanENN m (fun G => kappaKindENN q A G * h m G) else 0) ∧
  (∀ (V : Type u) [Fintype V], ∀ q : ℕ, 3 ≤ q → 2 ≤ Fintype.card V →
    ∀ (A : MGraph V → Pair V → Prop) (h w : MGraph V → ℝ≥0∞),
      kindInvariant A → (∀ G e, A G e → FrozenPair q G e) →
      (∀ (π : Equiv.Perm V) G, h (relabel π G) = h G) →
      RelabelLawInvariant w → (∑' G, w G) = 1 → ∀ e : Pair V,
        graphLawMeanENN w (fun G => kappaKindENN q A G * h G) =
          graphLawMeanENN w (fun G => if A G e then h G else 0))

/-- lem:pre-lifetime; finite conversion is part of the contract, not a convention. -/
def PreLifetimeStatement : Prop :=
  ∀ (V : Type u) [Fintype V], ∀ q : ℕ, 3 ≤ q → 2 ≤ Fintype.card V →
    (∀ G : MGraph V, Loopless G →
      (¬ Colorable q G → lifetime q G = 0 ∧ ∀ b, truncatedLifetime q b G = 0) ∧
      (∀ b : ℕ, 0 ≤ truncatedLifetime q b G ∧
        ENNReal.ofReal (truncatedLifetime q b G) ≤ lifetime q G ∧
        truncatedLifetime q b G ≤ b) ∧
      (∀ b b' : ℕ, b ≤ b' → truncatedLifetime q b G ≤ truncatedLifetime q b' G) ∧
      (Colorable q G → ∀ b : ℕ, 1 ≤ b → 1 ≤ truncatedLifetime q b G) ∧
      (2*q ≤ Fintype.card V →
        lifetime q G ≤ ENNReal.ofReal (lifetimeConstant q * Fintype.card V) ∧
        lifetime q G < ⊤ ∧ Summable (survival q G) ∧
        lifetimeReal q G = ∑' k : ℕ, survival q G k)) ∧
    (∀ G G' : MGraph V, subgraph G G' → lifetime q G' ≤ lifetime q G ∧
      ∀ b, truncatedLifetime q b G' ≤ truncatedLifetime q b G) ∧
    (∀ G : MGraph V, 0 < kappa q G → lifetime q G ≤ ENNReal.ofReal (1 / kappa q G)) ∧
    (∀ m : ℕ, graphMeanENN m (fun G : MGraph V => lifetime q G) =
      ∑' k : ℕ, ENNReal.ofReal (processSurvival (V := V) q (m+k)))

/-- Relabeling transport and law invariance consumed by Section 5. -/
def PreRelabelStatement : Prop :=
  ∀ (V : Type u) (W : Type v) [Fintype V] [Fintype W]
    (e : V ≃ W) (q : ℕ) (G : MGraph V),
    (Colorable q (relabel e G) ↔ Colorable q G) ∧
    (∀ a, degree (relabel e G) (e a) = degree G a) ∧
    (∀ a b, Frozen q (relabel e G) (e a) (e b) ↔ Frozen q G a b) ∧
    lifetime q (relabel e G) = lifetime q G ∧
    (∀ b, truncatedLifetime q b (relabel e G) = truncatedLifetime q b G) ∧
    (∀ m (h : MGraph W → ℝ), graphMean m (fun F : MGraph V => h (relabel e F)) =
      graphMean m h)

/-- lem:pre-classmass. -/
def PreClassmassStatement : Prop :=
  ∀ (V : Type u) [Fintype V], ∀ q : ℕ, 3 ≤ q → 2*q ≤ Fintype.card V →
    ∀ G : MGraph V, Loopless G → Colorable q G → ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < lifetime q G → classMass q G ≤ (1 + lifetimeConstant q) / y ∧
      ∀ C ∈ frozenClasses q G,
        (C.card : ℝ) ≤ (Fintype.card V : ℝ) * Real.sqrt ((1 + lifetimeConstant q) / y)

/-- def/lem:pre-quantile, including the exact capped distribution. -/
def PreQuantileStatement : Prop :=
  ∀ q n M : ℕ, 3 ≤ q → 2 ≤ n → ∀ η : ℝ, 0 < η → η ≤ 1/2 →
    let L := lowerQuantile (V := Fin n) q M η
    let U := upperQuantile (V := Fin n) q M η
    L ≤ U ∧ U ≤ M ∧ η ≤ cappedCDF (V := Fin n) q M L ∧
      η ≤ cappedTail (V := Fin n) q M U ∧
      (∀ m : ℕ, m ≤ M → cappedTail (V := Fin n) q M m =
        processSurvival (V := Fin n) q m) ∧
      (∀ m : ℕ, m < M → cappedCDF (V := Fin n) q M m =
        1 - processSurvival (V := Fin n) q (m+1)) ∧
      (∀ m : ℕ, m ≤ L → 1 - η < processSurvival (V := Fin n) q m) ∧
      (∀ m : ℕ, U < m → m ≤ M → processSurvival (V := Fin n) q m < η)

/-- lem:pre-poisson and normalization/integrability of its kernels. -/
def PrePoissonStatement : Prop :=
  (∀ z : ℝ, 0 ≤ z → Summable (poissonWeight z) ∧
    (∑' k : ℕ, poissonWeight z k) = 1 ∧ (∀ k, 0 ≤ poissonWeight z k)) ∧
  (∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    ∀ (h : MGraph V → ℝ≥0∞) (p : ℝ), 0 < p →
      (∫⁻ t in Set.Ioi (0 : ℝ), poissonGraphMeanENN (p*t) h) =
        ENNReal.ofReal (1/p) * ∑' m : ℕ, graphMeanENN m h) ∧
  (∀ (p : ℝ) (m : ℕ), 0 < p →
    IntegrableOn (fun t : ℝ => poissonWeight (p*t) m) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), poissonWeight (p*t) m) = 1/p)

/-- lem:pre-split(a): joint masses of the labeled subsequences. -/
def PreSplitListsStatement : Prop :=
  ∀ (E : Type u) [Fintype E] (J : ℕ), 1 ≤ J →
    ∀ (ν : E → ℝ) (label : E → Fin J) (μ : ℝ),
      (∀ e, 0 ≤ ν e) → (∑ e, ν e) = 1 → 0 ≤ μ → ∀ ys : Fin J → List E,
      (∀ j, ∀ e ∈ ys j, label e = j) →
      (∀ j, 0 < ∑ e : E, if label e = j then ν e else 0) →
      weightedListMean μ ν (fun xs => indicator (∀ j, splitSublist label j xs = ys j)) =
        ∏ j : Fin J,
          poissonListMass (μ * ∑ e : E, if label e = j then ν e else 0)
            (fun e => ν e / (∑ a : E, if label a = j then ν a else 0)) (ys j)

/-- lem:pre-split(b), after relabeling the partition as A ⊕ B. -/
def PreSplitGraphStatement : Prop :=
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

/-- lem:pre-split(c), with the exact one-vertex time changes. -/
def PreSplitRootStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    ∀ (t : ℝ) (h : MGraph (Option V) → ℝ≥0∞), 0 ≤ t →
      poissonGraphMeanENN t h =
        poissonGraphMeanENN (((Fintype.card V : ℝ)-1)*t/((Fintype.card V : ℝ)+1))
          (fun B : MGraph V => uniformPoissonListMeanENN (2*t/((Fintype.card V : ℝ)+1))
            (fun xs => h (addRoot B xs)))
def PreSplitStatement : Prop :=
  PreSplitListsStatement.{u} ∧ PreSplitGraphStatement.{u, v} ∧ PreSplitRootStatement.{u} ∧
  (∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    ∀ (t : ℝ) (h : MGraph V → ℝ≥0∞), 0 ≤ t →
      poissonGraphMeanENN t h = independentPoissonGraphMeanENN (looplessRate t) h)

/-- lem:pre-tails(a)--(d); thresholds in the Poisson assertions are real. -/
def PreTailsStatement : Prop :=
  (∀ m : ℕ, 1 ≤ m → ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∀ k : ℕ, 1 ≤ k →
    binomialTail m p k ≤ (m.choose k : ℝ) * p^k ∧
      (m.choose k : ℝ) * p^k ≤ (Real.exp 1 * m * p / k)^k) ∧
  (∀ μ k : ℝ, 0 ≤ μ → μ < k →
    poissonTail μ k ≤ Real.rpow (Real.exp 1 * μ / k) k) ∧
  (∀ μ s : ℝ, 0 < μ → 0 < s →
    poissonTail μ (μ+s) ≤ Real.exp (-(s^2)/(2*(μ+s))) ∧
    poissonLowerTail μ (μ-s) ≤ Real.exp (-(s^2)/(2*μ))) ∧
  (∀ z : ℝ, 0 ≤ z → ∀ i : ℕ, 1 ≤ i →
    poissonTail z i ≤ (Real.exp z - 1) * poissonWeight z (i-1))

/-- lem:pre-cycles; q≥3 is essential for the colorability part. -/
def PreCyclesStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 3 ≤ q →
    ∀ G : MGraph V, Loopless G → ConnectedSupport G → 2 ≤ (vertexSupport G).card →
      (edgeCount G ≤ (vertexSupport G).card → Colorable q G) ∧
      ((vertexSupport G).card + 1 ≤ edgeCount G → ThetaIn G ∨ DumbbellIn G)

/-- lem:pre-centre, both probability estimates and eventual quantile bounds. -/
def PreCentreStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    ∀ η : ℝ, 0 < η → η ≤ 1/2 →
      (∀ β : ℝ, gamma q < β → ∀ n : ℕ, 2*q ≤ n →
        processSurvival (V := Fin n) q (Nat.floor (β*n)) ≤
          ((q : ℝ)/((q : ℝ)-1) * Real.exp (2*β)) *
            Real.exp (-(n : ℝ)*(β-gamma q)*Real.log ((q : ℝ)/((q : ℝ)-1)))) ∧
      (∀ β : ℝ, gamma q < β → ∀ᶠ n : ℕ in atTop,
        lowerLocation q Λ η n ≤ upperLocation q Λ η n ∧
        (upperLocation q Λ η n : ℝ) ≤ β*n ∧ upperLocation q Λ η n < cap Λ n) ∧
      (∀ c : ℝ, 0 < c → c < 1/2 → ∃ C : ℝ, 0 < C ∧
        (∀ n : ℕ, 2*q ≤ n →
          1 - processSurvival (V := Fin n) q (Nat.floor (c*n)) ≤ C/n) ∧
        ∀ᶠ n : ℕ in atTop, c*n < (lowerLocation q Λ η n : ℝ))

/-- Cylinder sigma algebras and finite stopping rules used by Section 6. -/
def PreStoppingStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
    (∀ (m : ℕ) (A : Set (EdgeStream V)),
      @MeasurableSet _ (prefixSigma (V := V) m) A ↔ PrefixEvent m A) ∧
    (∀ q : ℕ, 3 ≤ q → IsStoppingTime (hittingTime (V := V) q)) ∧
    (∀ (a : V) (j : ℕ), IsStoppingTime (degreeHittingTime a j)) ∧
    (∀ T : EdgeStream V → WithTop ℕ, IsStoppingTime T → ∀ M : ℕ,
      ∃! t : EdgeTuple V M → WithTop ℕ, IsFiniteStoppingTime t ∧
        ∀ ω : EdgeStream V, t (fun i => ω i.val) = min (T ω) M)

/-- lem:red-deletion, including the occurrence identity and variance bound. -/
def RedDeletionStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ → ∀ n : ℕ, 2*q ≤ n →
      let L := lowerLocation q Λ η n
      let U := upperLocation q Λ η n
      (∑ i : Fin U, uniformMean (fun x : EdgeTuple (Fin n) U =>
        ((deletionYMinus q L i x : ℝ) - (deletionY q L x : ℝ))^2)) =
          terminalWindow (V := Fin n) q L U (fun m G _ =>
            ((m+1 : ℕ) : ℝ) * (2 * truncatedLifetime q (U-m) G - 1)) ∧
      variance (fun x : EdgeTuple (Fin n) U => (deletionY q L x : ℝ)) ≤
        2 * U * truncatedTerminalLifetime (V := Fin n) q L U (window q Λ η n)
/-- lem:red-varlower. -/
def RedVarlowerStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ → ∀ n : ℕ, 2*q ≤ n →
      let L := lowerLocation q Λ η n
      let U := upperLocation q Λ η n
      η^2 * (window q Λ η n)^2 ≤
        variance (fun x : EdgeTuple (Fin n) U => (deletionY q L x : ℝ))
/-- prop:red-window. -/
def RedWindowStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ → ∀ n : ℕ, 2*q ≤ n → ∀ K₀ : ℝ, 0 ≤ K₀ →
      truncatedTerminalLifetime (V := Fin n) q
        (lowerLocation q Λ η n) (upperLocation q Λ η n) (n*epsilon n) ≤ K₀*n*(epsilon n)^2 →
      window q Λ η n ≤ max 1 (2*Λ*K₀/η^2) * n * epsilon n
/-- prop:red-split: both exceptional events are restricted to L<H≤U. -/
def RedSplitStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ → ∀ n : ℕ, 2*q ≤ n →
      let L := lowerLocation q Λ η n
      let U := upperLocation q Λ η n
      lowWindowProbability (V := Fin n) q L U (degreeCut n) (lifetimeCut n) ≤ epsilon n →
      highLongWindowProbability (V := Fin n) q L U (degreeCut n) (lifetimeCut n) ≤ epsilon n →
      truncatedTerminalLifetime (V := Fin n) q L U (n*epsilon n) ≤ 3*n*(epsilon n)^2 ∧
        window q Λ η n ≤ (6*Λ/η^2)*n*epsilon n

/-- thm:low-main: one onset works for every y>0. -/
def LowMainStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, max 3 (2*q) ≤ N ∧
    ∀ n : ℕ, N ≤ n → ∀ y : ℝ, 0 < y →
      lowTerminalProbability (V := Fin n) q (degreeCut n) y ≤
        C * Real.rpow y (-(1 : ℝ)/2) * Real.rpow (n : ℝ) ((3 : ℝ)/8)
/-- cor:low, also restricted to any finite terminal window. -/
def CorLowStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ N : ℕ, max 3 (2*q) ≤ N ∧ ∀ n : ℕ, N ≤ n →
    lowTerminalProbability (V := Fin n) q (degreeCut n) (lifetimeCut n) ≤ epsilon n ∧
      ∀ L U : ℕ, L ≤ U →
        lowWindowProbability (V := Fin n) q L U (degreeCut n) (lifetimeCut n) ≤ epsilon n
/-- thm:high-main; the analytic onset depends on Λ alone. -/
def HighMainStatement : Prop :=
  (∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, 0 < Λ → ∀ n : ℕ, 3 ≤ n →
    pivotalCut Λ ≤ descentCut n →
      highTerminalProbability (V := Fin n) q (cap Λ n) (degreeCut n) ≤ highBound Λ n) ∧
  (∀ Λ : ℝ, 0 < Λ → ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    pivotalCut Λ ≤ descentCut n ∧ highBound Λ n ≤ epsilon n ∧
      ∀ q : ℕ, 3 ≤ q → ∀ L U : ℕ, L ≤ U → U ≤ cap Λ n →
        highWindowProbability (V := Fin n) q L U (degreeCut n) ≤ epsilon n)
/-- thm:proof-window at Λ=γ_q+2. -/
def ProofWindowStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ η : ℝ, 0 < η → η ≤ etaZero (capDensity q) →
    ∃ N : ℕ, max 3 (2*q) ≤ N ∧ ∀ n : ℕ, N ≤ n →
      window q (capDensity q) η n ≤ (6*capDensity q/η^2)*n*epsilon n
/-- Section 7's summable error and its asymptotic scales. -/
def EpsilonAdmissibleStatement : Prop :=
  AdmissibleError epsilon ∧ Tendsto epsilon atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ)*epsilon n) atTop atTop

/-- lem:conv-interp. -/
def ConvInterpStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ n₁ n₂ : ℕ, 1 ≤ n₁ → 1 ≤ n₂ →
    ∀ c : ℝ, 0 ≤ c → rho q n₁ c * rho q n₂ c ≤ rho q (n₁+n₂) c
/-- lem:conv-quantile, uniformly over 0<c≤Λ after its cutoff. -/
def ConvQuantileStatement : Prop :=
  (∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ c : ℝ, 0 ≤ c →
    rho q n c = Real.exp (-c) *
      poissonMixture (c*((n : ℝ)-1)) (processSurvival (V := Fin n) q)) ∧
  (∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    ∀ η : ℝ, 0 < η → η ≤ 1/2 →
      ∃ N : ℕ, 2*q ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ c : ℝ, 0 < c → c ≤ Λ →
        (c*((n : ℝ)-1) ≤ (lowerLocation q Λ η n : ℝ) - poissonDeviation n →
          Real.exp (-Λ)*(1-η)*(1-poissonTailError Λ n) ≤ rho q n c) ∧
        ((upperLocation q Λ η n : ℝ) + poissonDeviation n ≤ c*((n : ℝ)-1) →
          rho q n c ≤ η + poissonTailError Λ n))
/-- lem:conv-superadd, using the supplied window constant. -/
def ConvSuperaddStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    ∀ δ : ℕ → ℝ, AdmissibleError δ → ∀ η : ℝ, 0 < η → η ≤ etaZero Λ →
      ∀ (K : ℝ) (N : ℕ), 0 < K →
        (∀ n : ℕ, max (2*q) N ≤ n → window q Λ η n ≤ K*n*δ n) →
        ∃ s₀ : ℕ, 2*q ≤ s₀ ∧
          ComparisonHypotheses (xi q Λ η) (comparisonError δ Λ K) s₀
/-- lem:conv-tree, with eventual antitonicity of the error. -/
def ConvTreeStatement : Prop :=
  ∀ u₀ : ℝ, 1 ≤ u₀ → ∀ g : ℝ → ℝ,
    (∀ x : ℝ, 1 ≤ x → 0 < g x) → AntitoneOn g (Set.Ici u₀) →
    Summable (fun k : ℕ => g (Real.exp ((k : ℝ)+1))) →
    ∀ (s₀ : ℕ) (ξ : ℕ → ℝ), ComparisonHypotheses ξ g s₀ →
      (∃ C : ℝ, ∀ n : ℕ, s₀ ≤ n → |ξ n| ≤ C) →
      ∃ a : ℝ, Tendsto ξ atTop (𝓝 a)
/-- lem:conv-transfer, including exact binomial mixing. -/
def ConvTransferStatement : Prop :=
  (∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, 0 < Λ →
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ m : ℕ, (m : ℝ) ≤ Λ*n →
      m ≤ n.choose 2 ∧
      1 - simpleProbability (V := Fin n) q m ≤
        Real.exp (2*Λ^2+1)*(1-processSurvival (V := Fin n) q m) ∧
      simpleProbability (V := Fin n) q m ≤
        Real.exp (2*Λ^2+1)*processSurvival (V := Fin n) q m) ∧
  (∀ q n : ℕ, 3 ≤ q → 2 ≤ n →
    (∀ a b : ℕ, a ≤ b → b ≤ n.choose 2 →
      simpleProbability (V := Fin n) q b ≤ simpleProbability (V := Fin n) q a) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      bernoulliProbability (V := Fin n) q p =
        ∑ j ∈ Finset.range (n.choose 2 + 1),
          binomialWeight (n.choose 2) p j * simpleProbability (V := Fin n) q j) ∧
    (∀ (m : ℕ) (p : ℝ), m ≤ n.choose 2 → 0 ≤ p → p ≤ 1 →
      simpleProbability (V := Fin n) q m *
          (∑ j ∈ Finset.range (m+1), binomialWeight (n.choose 2) p j) ≤
        bernoulliProbability (V := Fin n) q p ∧
      bernoulliProbability (V := Fin n) q p ≤ simpleProbability (V := Fin n) q m +
        ∑ j ∈ Finset.range m, binomialWeight (n.choose 2) p j))
/-- thm:red-convergence, proved in Appendix A: one witness for all conclusions. -/
def RedConvergenceStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    ∀ δ : ℕ → ℝ, AdmissibleError δ → WindowBound q Λ δ →
      ∃ α : ℝ, α ∈ Set.Icc (1/2 : ℝ) (gamma q) ∧ QuantileLimits q Λ α ∧
        ProcessLimits q α ∧ SimpleLimits q α ∧ BinomialLimits q α
end ThresholdFoundations

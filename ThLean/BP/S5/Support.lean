module

public import ThLean.Defs

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S5
open ThresholdFoundations

/-! Local notation and explicit finite/countable kernels for Section 5. -/

def partnerCount {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V) (a : V) : ℕ :=
  frozenPartnerCount q G a

abbrev Outside {V : Type*} (a : V) := {v : V // v ≠ a}

def outsideGraph {V : Type*} [Fintype V] (G : MGraph V) (a : V) : MGraph (Outside a) :=
  withoutVertex G a

def rootMap {V : Type*} (a : V) : Option (Outside a) → V :=
  fun v => v.elim a Subtype.val

def rebuild {V : Type*} [Fintype V] (G : MGraph V) (a : V) (xs : List (Outside a)) :
    MGraph V := mapGraph (rootMap a) (addRoot (outsideGraph G a) xs)

def listMean {V : Type*} [Fintype V] (k : ℕ) (f : List V → ℝ) : ℝ :=
  uniformMean (fun x : Fin k → V => f (List.ofFn x))

def lawMean {V : Type*} [Fintype V] (ν : PMF (MGraph V)) (f : MGraph V → ℝ) : ℝ :=
  ∑' G, (ν G).toReal * f G

def invariantLaw {V : Type*} [Fintype V] (ν : PMF (MGraph V)) : Prop :=
  ∀ π : Equiv.Perm V, ν.map (relabel π) = ν

def perPairRate {V : Type*} (r : ℝ) (e : Sym2 V) : ℝ :=
  if ∃ v, e = s(v, v) then 0 else r

def countMean {V : Type*} [Fintype V] (r : ℝ) (f : MGraph V → ℝ) : ℝ :=
  independentPoissonGraphMean (perPairRate r) f

def blocking {V : Type*} [Fintype V] (q : ℕ) (B : MGraph V) (j : ℕ) : ℝ :=
  listMean j (fun xs => indicator (Colorable q B ∧ ¬ Colorable q (addRoot B xs)))

def increment {V : Type*} [Fintype V] (q : ℕ) (B : MGraph V) (j : ℕ) : ℝ :=
  uniformMean (fun x : Fin (j + 1) → V =>
    indicator (Colorable q (addRoot B (List.ofFn (fun i : Fin j => x i.castSucc))) ∧
      ¬ Colorable q (addRoot B (List.ofFn x))))

def blockingMean {V : Type*} [Fintype V] (q : ℕ) (r : ℝ) (j : ℕ) : ℝ :=
  countMean r (fun B : MGraph V => blocking q B j)

def incrementMean {V : Type*} [Fintype V] (q : ℕ) (r : ℝ) (j : ℕ) : ℝ :=
  countMean r (fun B : MGraph V => increment q B j)

def addedFailure {V : Type*} [Fintype V] (q : ℕ) (r z : ℝ) : ℝ :=
  poissonMixture z (blockingMean (V := V) q r)

def wordFiberCard {E : Type*} [Fintype E] (c : E → ℕ) : ℕ :=
  Fintype.card {x : Fin (∑ e, c e) → E // ∀ e,
    (Finset.univ.filter (fun i => x i = e)).card = c e}

def completionKernel {V : Type*} [Fintype V] (D : ℕ) (xs : List V)
    (Z : UniformSubset V D) : ℝ :=
  ThresholdFoundations.completionKernel D xs Z.val

def permSubset {V : Type*} [Fintype V] (D : ℕ) (π : Equiv.Perm V)
    (Z : UniformSubset V D) : UniformSubset V D :=
  ⟨Z.val.map π.toEmbedding, by simpa using Z.property⟩

def lowKappa {V : Type*} [Fintype V] (q D : ℕ) (G : MGraph V) : ℝ :=
  kappaKind q (fun F e => lowEdge F D e) G

def lowObservable {V : Type*} [Fintype V] (q D : ℕ) (y : ℝ) (G : MGraph V) : ℝ :=
  lowKappa q D G * indicator (ENNReal.ofReal y < lifetime q G)

def rootEvent {V : Type*} [Fintype V] (q D : ℕ) (a : V) (G : MGraph V) : Prop :=
  degree G a ≤ D ∧ 0 < partnerCount q G a

def rootProbability {V : Type*} [Fintype V] (q D : ℕ) (a : V) (t : ℝ) : ℝ :=
  poissonGraphMean t (fun G => indicator (rootEvent q D a G))

def advanceReal (q N D : ℕ) : ℝ := (identificationAdvance (V := Fin N) q D).toReal

def nmTime (q N D : ℕ) (t : ℝ) : ℝ :=
  poissonGraphMean t (nmProbability (V := Fin N) q D)

def lowTime (q n D : ℕ) (y t : ℝ) : ℝ :=
  poissonGraphMean t (lowObservable (V := Fin n) q D y)

def windowLow (q n D : ℕ) (y : ℝ) (L U : ℕ) : ℝ :=
  ThresholdFoundations.lowWindowProbability (V := Fin n) q L U D y

def discrepancy (q N D : ℕ) (t : ℝ) : ℝ :=
  poissonGraphMean t (identificationFailureProbability (V := Fin N) q D)

def rawIdentificationBound (q N D k : ℕ) : ℝ :=
  2 * q + 2 * (q : ℝ)^2 * (Real.log q)^2 * (D : ℝ)^2 +
    lowTimeCap q N * (Real.exp 1 * D * lowMeanBound q / k)^k +
    2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ)^k

def identificationBound (q N D k : ℕ) : ℝ :=
  identificationConstant q * ((D : ℝ)^k +
    N * (Real.exp 1 * D * lowMeanBound q / k)^k + (D : ℝ)^2 + 1)

def GoodSize (q n : ℕ) : Prop :=
  16 ≤ n ∧ lowSizeOnset q ≤ n - 1 ∧
  0 < Real.log (Real.log n) ∧
  Real.log (Real.exp 1 * lowMeanBound q * Real.log (Real.log n)) ≤
    (1 / 8 : ℝ) * Real.log (Real.log n) ∧
  (n : ℝ)^(1 / 4 : ℝ) * (Real.log n)^(1 / 4 : ℝ) +
    (Real.log n)^(1 / 2 : ℝ) + 1 ≤ (n : ℝ)^(3 / 8 : ℝ)

end ThLean.BP.S5

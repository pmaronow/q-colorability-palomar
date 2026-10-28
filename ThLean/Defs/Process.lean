import ThLean.Defs.High

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

variable {V : Type*} [Fintype V]

/-! ## Prefixes, finite laws, lifetimes and terminal expectations -/

abbrev EdgeTuple (V : Type*) (m : ℕ) := Fin m → Pair V
abbrev EdgeStream (V : Type*) := ℕ → Pair V

def tupleGraph {m : ℕ} (x : EdgeTuple V m) : MGraph V :=
  fun e => (Finset.univ.filter (fun i => (x i).val = e)).card

def tuplePrefix {M : ℕ} (x : EdgeTuple V M) (m : ℕ) : MGraph V :=
  fun e => (Finset.univ.filter (fun i => i.val < m ∧ (x i).val = e)).card

def deletedPrefix {M : ℕ} (x : EdgeTuple V M) (i : Fin M) (m : ℕ) : MGraph V :=
  fun e => (Finset.univ.filter (fun j => j.val < m ∧ j ≠ i ∧ (x j).val = e)).card

def deletionDisagreement {M : ℕ} (q : ℕ) (x : EdgeTuple V M) (i : Fin M) (m : ℕ) : Prop :=
  Colorable q (deletedPrefix x i m) ∧ ¬ Colorable q (tuplePrefix x m)

def processGraph (ω : EdgeStream V) (m : ℕ) : MGraph V :=
  tupleGraph (fun i : Fin m => ω i.val)

/-- `none` in `WithTop ℕ` means infinity, never time zero. -/
def firstFailure (P : ℕ → Prop) : WithTop ℕ :=
  if h : ∃ m, P m then (Nat.find h : WithTop ℕ) else ⊤

def hittingTime (q : ℕ) (ω : EdgeStream V) : WithTop ℕ :=
  firstFailure (fun m => ¬ Colorable q (processGraph ω m))

def freshHittingTime (q : ℕ) (G : MGraph V) (ω : EdgeStream V) : WithTop ℕ :=
  firstFailure (fun k => ¬ Colorable q (G + processGraph ω k))

/-- Optional terminal state; nothing is assigned on the event `H=∞`. -/
def lastGraph (q : ℕ) (ω : EdgeStream V) : Option (MGraph V) :=
  if h : ∃ m, ¬ Colorable q (processGraph ω m) then
    some (processGraph ω (Nat.find h - 1)) else none

/-- Stream coordinate zero is the paper's edge `e_1`. Used for `q≥1`. -/
def finalEdge (q : ℕ) (ω : EdgeStream V) : Option (Pair V) :=
  if h : ∃ m, ¬ Colorable q (processGraph ω m) then
    some (ω (Nat.find h - 1)) else none

def survival (q : ℕ) (G : MGraph V) (k : ℕ) : ℝ :=
  uniformProb (fun x : EdgeTuple V k => Colorable q (G + tupleGraph x))

def processSurvival (q : ℕ) (m : ℕ) : ℝ := survival q (0 : MGraph V) m

def hittingMass (q k : ℕ) : ℝ :=
  processSurvival (V := V) q k - processSurvival (V := V) q (k + 1)

/-- Infimum of the decreasing tails; the mass assigned to H=∞. -/
def infiniteHittingProbability (q : ℕ) : ℝ :=
  sInf (Set.range (processSurvival (V := V) q))

def hittingWindowProbability (q : ℕ) (a : ℤ) (w : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Nat.floor ((a : ℝ) + w)),
    if |((k + 1 : ℕ) : ℝ) - (a : ℝ)| ≤ w then hittingMass (V := V) q k else 0

/-- Def. pre-lifetime: the canonical `r` is extended-valued. -/
def lifetime (q : ℕ) (G : MGraph V) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (survival q G k)

def truncatedLifetime (q b : ℕ) (G : MGraph V) : ℝ :=
  ∑ k ∈ Finset.range b, survival q G k

/-- Eq. red-weight; the guard is essential for nonnegative terminal weights. -/
def deletionWeight (q b : ℕ) (G : MGraph V) : ℝ :=
  if Colorable q G then 2 * truncatedLifetime q b G - 1 else 0

/-- Use only after proving `lifetime q G < ∞`, e.g. for `|V|≥2*q`. -/
def lifetimeReal (q : ℕ) (G : MGraph V) : ℝ := (lifetime q G).toReal

def terminalStepENN (q m : ℕ) (h : MGraph V → Pair V → ℝ≥0∞) : ℝ≥0∞ :=
  uniformMeanENN (fun x : EdgeTuple V m =>
    uniformMeanENN (fun e : Pair V =>
      if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
      then h (tupleGraph x) e else 0))

/-- Lem. pre-terminal: sum over disjoint finite hitting times, excludes `∞`. -/
def terminalMeanENN (q : ℕ) (h : MGraph V → Pair V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' m : ℕ, terminalStepENN q m h

def terminalProbability (q : ℕ) (A : MGraph V → Pair V → Prop) : ℝ :=
  (terminalMeanENN q (fun G e => if A G e then 1 else 0)).toReal

def terminalWindowMean (q L U : ℕ) (h : MGraph V → ℝ) : ℝ :=
  ∑ m ∈ Finset.Ico L U,
    uniformMean (fun x : EdgeTuple V m => kappa q (tupleGraph x) * h (tupleGraph x))

def lowEdge (G : MGraph V) (D : ℕ) (e : Pair V) : Prop :=
  ∃ u, Touches u e.val ∧ degree G u ≤ D
def highEdge (G : MGraph V) (D : ℕ) (e : Pair V) : Prop :=
  ∃ u, Touches u e.val ∧ D < degree G u
def bothHigh (G : MGraph V) (D : ℕ) (e : Pair V) : Prop :=
  ∀ u, Touches u e.val → D < degree G u

def lowTerminalProbability (q D : ℕ) (y : ℝ) : ℝ :=
  terminalProbability (V := V) q (fun G e => lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G)

def highTerminalProbability (q M D : ℕ) : ℝ :=
  (∑ m ∈ Finset.range M,
    terminalStepENN (V := V) q m (fun G e => if highEdge G D e then 1 else 0)).toReal

/-! ## Cylinders and stopping times, without an infinite probability measure -/

def AgreeUpTo (m : ℕ) (ω ω' : EdgeStream V) : Prop :=
  ∀ i, i < m → ω i = ω' i

def PrefixEvent (m : ℕ) (A : EdgeStream V → Prop) : Prop :=
  ∀ ω ω', AgreeUpTo m ω ω' → (A ω ↔ A ω')

/-- Actual sigma-algebra of the first m coordinates (discrete finite target). -/
@[instance_reducible] def prefixSigma (m : ℕ) : MeasurableSpace (EdgeStream V) :=
  MeasurableSpace.comap (fun ω (i : Fin m) => ω i.val) ⊤

def IsStoppingTime (T : EdgeStream V → WithTop ℕ) : Prop :=
  ∀ m : ℕ, PrefixEvent m (fun ω => T ω ≤ (m : WithTop ℕ))

def stoppedTime (q M : ℕ) (ω : EdgeStream V) : WithTop ℕ :=
  min (hittingTime q ω) (M : WithTop ℕ)

def degreeHittingTime (u : V) (j : ℕ) (ω : EdgeStream V) : WithTop ℕ :=
  firstFailure (fun m => j ≤ degree (processGraph ω m) u)

def phi (q : ℕ) (u : V) (ω : EdgeStream V) (m : ℕ) : ℝ :=
  potential q (processGraph ω m) u

def psi (q : ℕ) (u : V) (ω : EdgeStream V) (m : ℕ) : ℝ :=
  creditIncrement q (processGraph ω m) u (ω m)

/-- Finite counterpart of an F_m-measurable stopping-time event. -/
def IsFiniteStoppingTime {M : ℕ} (T : EdgeTuple V M → WithTop ℕ) : Prop :=
  ∀ (m : ℕ) (x y : EdgeTuple V M),
    (∀ i : Fin M, i.val < m → x i = y i) →
    (T x ≤ (m : WithTop ℕ) ↔ T y ≤ (m : WithTop ℕ))

def stoppedOccupation {M : ℕ} (q : ℕ) (u : V)
    (T : EdgeTuple V M → WithTop ℕ) (x : EdgeTuple V M) : ℝ :=
  ∑ m ∈ Finset.range M,
    if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
    then beta q (tuplePrefix x m) u else 0

end ThresholdFoundations

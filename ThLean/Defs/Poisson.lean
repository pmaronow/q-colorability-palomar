module

public import ThLean.Defs.Simple

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

/-! ## Fixed-time Poisson laws (pre-poisson, pre-split, Appendix A) -/

/-- Algebraic extension to all real z is intentional for Appendix A.
Probability claims always assume z≥0. At z=0 Lean has 0^0=1. -/
def poissonWeight (z : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-z) * z ^ k / (Nat.factorial k : ℝ)

def poissonMixture (z : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, poissonWeight z k * a k

def poissonMixtureENN (z : ℝ) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (poissonWeight z k) * a k

def binomialWeight (m : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  if k ≤ m then (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0

def poissonGraphMean {V : Type*} [Fintype V] (t : ℝ) (h : MGraph V → ℝ) : ℝ :=
  poissonMixture t (fun m => uniformMean (fun x : EdgeTuple V m => h (tupleGraph x)))

def poissonGraphMeanENN {V : Type*} [Fintype V]
    (t : ℝ) (h : MGraph V → ℝ≥0∞) : ℝ≥0∞ :=
  poissonMixtureENN t (fun m => uniformMeanENN (fun x : EdgeTuple V m => h (tupleGraph x)))

/-- Equivalent fixed-time histogram law; particularly convenient for splitting.
All rates must be nonnegative in probability lemmas. -/
def independentPoissonGraphMass {V : Type*} [Fintype V]
    (rate : Sym2 V → ℝ) (G : MGraph V) : ℝ :=
  ∏ e : Sym2 V, poissonWeight (rate e) (G e)

def independentPoissonGraphMean {V : Type*} [Fintype V]
    (rate : Sym2 V → ℝ) (h : MGraph V → ℝ) : ℝ :=
  ∑' G : MGraph V, independentPoissonGraphMass rate G * h G

abbrev PoissonPrefix (V : Type*) := Σ m : ℕ, EdgeTuple V m
def poissonPrefixState {V : Type*} [Fintype V] (x : PoissonPrefix V) : MGraph V :=
  tupleGraph x.2

def poissonPrefixMass {V : Type*} [Fintype V] (t : ℝ) (x : PoissonPrefix V) : ℝ :=
  poissonWeight t x.1 / (Fintype.card (EdgeTuple V x.1) : ℝ)

/-- If a clock is supplied, this is exactly G(Pi_t); proofs use its fixed-time
mixture above and never require constructing a path-space clock. -/
def poissonizedGraph {V : Type*} [Fintype V]
    (ω : EdgeStream V) (ticks : ℝ → ℕ) (t : ℝ) : MGraph V := processGraph ω (ticks t)

def poissonListMass {E : Type*} (z : ℝ) (ν : E → ℝ) (xs : List E) : ℝ :=
  poissonWeight z xs.length * (xs.map ν).prod

def weightedListMean {E : Type*} [Fintype E]
    (z : ℝ) (ν : E → ℝ) (f : List E → ℝ) : ℝ :=
  poissonMixture z (fun k => ∑ x : Fin k → E,
    (∏ i, ν (x i)) * f (List.ofFn x))

def splitSublist {E : Type*} {J : ℕ} (label : E → Fin J)
    (j : Fin J) (xs : List E) : List E := xs.filter (fun x => label x = j)

/-- Ordered independent endpoint samples, with diagonal values retained. -/
def orderedTupleGraph {V : Type*} [Fintype V] {m : ℕ}
    (x : Fin m → V × V) : MGraph V :=
  fun e => (Finset.univ.filter (fun i => s((x i).1, (x i).2) = e)).card

abbrev OrderedPoissonPrefix (n : ℕ) := Σ m : ℕ, Fin m → Fin n × Fin n
def poissonModelA (n : ℕ) (x : OrderedPoissonPrefix n) : MGraph (Fin n) :=
  orderedTupleGraph x.2

/-- Ordered sampling gives rate c/n on a loop and 2c/n on a nonloop. -/
def poissonARate (n : ℕ) (c : ℝ) (e : Sym2 (Fin n)) : ℝ :=
  if ∃ v, e = s(v, v) then c / n else 2 * c / n

def poissonModelAMass (n : ℕ) (c : ℝ) (G : MGraph (Fin n)) : ℝ :=
  independentPoissonGraphMass (poissonARate n c) G

/-- Def. conv-poisson: A_n(c) uses Poisson mean c*n, NOT c*(n-1). -/
def rho (q n : ℕ) (c : ℝ) : ℝ :=
  poissonMixture (c * n) (fun m =>
    uniformProb (fun x : Fin m → Fin n × Fin n => Colorable q (orderedTupleGraph x)))

def leftVertex (n₁ n₂ : ℕ) (v : Fin n₁) : Fin (n₁ + n₂) := ⟨v.val, by omega⟩
def rightVertex (n₁ n₂ : ℕ) (v : Fin n₂) : Fin (n₁ + n₂) := ⟨n₁ + v.val, by omega⟩

def mixedGraph {n₁ n₂ k₀ k₁ k₂ : ℕ}
    (x₀ : Fin k₀ → Fin (n₁ + n₂) × Fin (n₁ + n₂))
    (x₁ : Fin k₁ → Fin n₁ × Fin n₁) (x₂ : Fin k₂ → Fin n₂ × Fin n₂) :
    MGraph (Fin (n₁ + n₂)) :=
  orderedTupleGraph x₀ + mapGraph (leftVertex n₁ n₂) (orderedTupleGraph x₁) +
    mapGraph (rightVertex n₁ n₂) (orderedTupleGraph x₂)

def interpolationCoefficient (q n₁ n₂ : ℕ) (k : Fin 3 → ℕ) : ℝ :=
  uniformMean (fun x₀ : Fin (k 0) → Fin (n₁ + n₂) × Fin (n₁ + n₂) =>
    uniformMean (fun x₁ : Fin (k 1) → Fin n₁ × Fin n₁ =>
      uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
        indicator (Colorable q (mixedGraph x₀ x₁ x₂)))))

/-- A*(mu) is represented by mixedGraph and these independent Poisson weights.
This real series, also for signed mu, is the analytic extension of bar-chi. -/
def chiBar (q n₁ n₂ : ℕ) (μ : Fin 3 → ℝ) : ℝ :=
  ∑' k : Fin 3 → ℕ, (∏ i : Fin 3, poissonWeight (μ i) (k i)) *
    interpolationCoefficient q n₁ n₂ k

def interpolationMeans (n₁ n₂ : ℕ) (c θ : ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then ((n₁ + n₂ : ℕ) : ℝ) * θ
  else if i = 1 then (n₁ : ℝ) * (c - θ) else (n₂ : ℝ) * (c - θ)

def chi (q n₁ n₂ : ℕ) (c θ : ℝ) : ℝ :=
  chiBar q n₁ n₂ (interpolationMeans n₁ n₂ c θ)

end ThresholdFoundations

module

public import ThLean.Defs

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.SA
open ThresholdFoundations

/-- Window control at a fixed quantile level; eq:conv-window. -/
def WindowAt (q : ℕ) (Λ : ℝ) (δ : ℕ → ℝ) (η K : ℝ) (n₁ : ℕ) : Prop :=
  0 < K ∧ ∀ n : ℕ, max (2 * q) n₁ ≤ n → window q Λ η n ≤ K * n * δ n

/-- Both comparisons in eq:conv-superadd, using the frozen predicate. -/
abbrev Compares := ComparisonHypotheses

/-- Real envelope for the discontinuous ceiling error. -/
def envelope (u : ℝ) : ℝ := Real.log u / Real.sqrt u

def WindowFamily (q : ℕ) (Λ : ℝ) (δ : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ etaZero Λ → ∃ K : ℝ, ∃ n₁ : ℕ, WindowAt q Λ δ η K n₁

/-- Argument-order adapters for the frozen finite-support functionals. -/
abbrev supportWeight {D : Type} [Fintype D] (rates : D → ℝ) (T : Finset D) : ℝ :=
  poissonSupportWeight rates T
abbrev supportMean {D : Type} [Fintype D] (F : Finset D → ℝ) (rates : D → ℝ) : ℝ :=
  poissonSupportMean rates F
abbrev TaggedMark := InterpolationMark
abbrev markEdge {n₁ n₂ : ℕ} : TaggedMark n₁ n₂ → Sym2 (Fin (n₁ + n₂)) :=
  interpolationMarkEdge
abbrev supportGraph {n₁ n₂ : ℕ} (T : Finset (TaggedMark n₁ n₂)) : MGraph (Fin (n₁ + n₂)) :=
  ThresholdFoundations.supportGraph interpolationMarkEdge T
abbrev markRate (n₁ n₂ : ℕ) (μ : Fin 3 → ℝ) : TaggedMark n₁ n₂ → ℝ :=
  interpolationMarkRate μ
abbrev finiteChiBar := chiSupport

def finiteChi (q n₁ n₂ : ℕ) (c θ : ℝ) : ℝ :=
  finiteChiBar q n₁ n₂ (interpolationMeans n₁ n₂ c θ)
abbrev drift := interpolationClassDrift

def driftMean (q n₁ n₂ : ℕ) (c θ : ℝ) : ℝ :=
  supportMean (fun T => drift q n₁ n₂ (supportGraph T))
    (markRate n₁ n₂ (interpolationMeans n₁ n₂ c θ))

def addLoss (q n₁ n₂ : ℕ) (j : Fin 3) (G : MGraph (Fin (n₁ + n₂))) : ℝ :=
  if j = 0 then
    uniformMean (fun xy : Fin (n₁ + n₂) × Fin (n₁ + n₂) =>
      indicator (Colorable q G ∧ ¬ Colorable q (addEdge G s(xy.1, xy.2))))
  else if j = 1 then
    uniformMean (fun xy : Fin n₁ × Fin n₁ =>
      indicator (Colorable q G ∧ ¬ Colorable q
        (addEdge G s(leftVertex n₁ n₂ xy.1, leftVertex n₁ n₂ xy.2))))
  else
    uniformMean (fun xy : Fin n₂ × Fin n₂ =>
      indicator (Colorable q G ∧ ¬ Colorable q
        (addEdge G s(rightVertex n₁ n₂ xy.1, rightVertex n₁ n₂ xy.2))))

abbrev leafList := BlockTree.leafWeights

def Halves : BlockTree → Prop
  | .leaf _ => True
  | .node a b => Halves a ∧ Halves b ∧
      a.leaves = (a.leaves + b.leaves + 1) / 2 ∧
      b.leaves = (a.leaves + b.leaves) / 2

def AnalyticError (u₀ : ℝ) (g : ℝ → ℝ) : Prop :=
  1 ≤ u₀ ∧ (∀ u : ℝ, 1 ≤ u → 0 ≤ g u) ∧
  AntitoneOn g (Set.Ici u₀) ∧ Summable (fun k : ℕ => g (Real.exp (k + 1 : ℝ)))

def binomialEvent (B : ℕ) (p : ℝ) (A : ℕ → Prop) : ℝ :=
  ∑ k ∈ Finset.range (B + 1), binomialWeight B p k * indicator (A k)
end ThLean.BP.SA

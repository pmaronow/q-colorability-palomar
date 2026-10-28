import ThLean.Defs.Quantile

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

/-! ## Named parameters and the abstract tree of Appendix A -/

def gamma (q : ℕ) : ℝ := Real.log (q : ℝ) / Real.log ((q : ℝ) / ((q : ℝ) - 1))
def capDensity (q : ℕ) : ℝ := gamma q + 2
def cap (Λ : ℝ) (n : ℕ) : ℕ := Nat.floor (Λ * n)
def etaZero (Λ : ℝ) : ℝ := Real.exp (-2 * Λ) / 8
def lifetimeConstant (q : ℕ) : ℝ := 2 * q * Real.log (q : ℝ) + 2 * q + 1
def epsilon (n : ℕ) : ℝ :=
  if n < 3 then 1 else Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ) / 2)
def lifetimeCut (n : ℕ) : ℝ := (n : ℝ) * epsilon n ^ 2
def degreeCut (n : ℕ) : ℕ := Nat.floor (Real.rpow (Real.log (n : ℝ)) ((1 : ℝ) / 4))
def pivotalCut (Λ : ℝ) : ℕ := Nat.ceil (8 * Λ)
def descentCut (n : ℕ) : ℕ := degreeCut n / 2
def lowTruncation (n : ℕ) : ℕ := Nat.ceil (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))
def lowMeanBound (q : ℕ) : ℝ := 4 * q * Real.log (q : ℝ) + 1
def identificationConstant (q : ℕ) : ℝ := 2 * Real.exp (lowMeanBound q)
def lowSizeOnset (q : ℕ) : ℕ := Nat.ceil (4 * q * Real.log (q : ℝ)) + 1
def lowEdgeRate (N : ℕ) : ℝ := 1 / (N.choose 2 : ℝ)
def lowTimeCap (q N : ℕ) : ℝ := 2 * q * Real.log (q : ℝ) * N
def neighborMean (N D : ℕ) (s : ℝ) : ℝ := lowEdgeRate N * (N - D : ℕ) * s
def augmentedRate (N D : ℕ) : ℝ := lowEdgeRate N * ((N - D + 1).choose 2 : ℝ)
def lowBoundConstant (q : ℕ) : ℝ :=
  8 * identificationConstant q * Real.sqrt (1 + lifetimeConstant q)
def poissonDeviation (n : ℕ) : ℕ := Nat.ceil (Real.sqrt (n : ℝ) * Real.log (n : ℝ))
def poissonTailError (Λ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((Real.log (n : ℝ)) ^ 2) / (2 * Λ))

def highBound (Λ : ℝ) (n : ℕ) : ℝ :=
  (8 / 3 : ℝ) * (4 : ℝ) ^ (-((degreeCut n + 1 - descentCut n : ℕ) : ℤ)) +
    (32 * Λ / (3 * Real.log 2)) * ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 *
      (Real.log (n : ℝ) / (descentCut n - pivotalCut Λ + 2 : ℕ)) *
      (2 * Real.exp 1 * Λ / descentCut n) ^ descentCut n

def lowerLocation (q : ℕ) (Λ η : ℝ) (n : ℕ) : ℕ :=
  lowerQuantile (V := Fin n) q (cap Λ n) η
def upperLocation (q : ℕ) (Λ η : ℝ) (n : ℕ) : ℕ :=
  upperQuantile (V := Fin n) q (cap Λ n) η
def window (q : ℕ) (Λ η : ℝ) (n : ℕ) : ℝ :=
  (upperLocation q Λ η n : ℝ) - (lowerLocation q Λ η n : ℝ)
def xi (q : ℕ) (Λ η : ℝ) (n : ℕ) : ℝ := (lowerLocation q Λ η n : ℝ) / n
def stepExtension (δ : ℕ → ℝ) (u : ℝ) : ℝ := δ (Nat.floor u)
def comparisonError (δ : ℕ → ℝ) (Λ K' u : ℝ) : ℝ :=
  K' * stepExtension δ u + (Λ + 6) * Real.log u / Real.sqrt u
def pathError (g : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  ∑' i : ℕ, g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1))

def AdmissibleError (δ : ℕ → ℝ) : Prop :=
  (∀ n, 1 ≤ n → 0 < δ n ∧ δ n ≤ 1) ∧
  (∀ n m, 1 ≤ n → n ≤ m → δ m ≤ δ n) ∧
  Summable (fun k : ℕ => δ (Nat.floor (Real.exp (k + 1 : ℝ))))

end ThresholdFoundations

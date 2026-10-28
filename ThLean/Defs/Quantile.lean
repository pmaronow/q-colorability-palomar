import ThLean.Defs.Process

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThresholdFoundations

variable {V : Type*} [Fintype V]

/-! ## Quantiles, clipping, and the deletion variables -/

/-- Equals `min(H-1,M)` for every stream extension, including `H=∞`. -/
def cappedLast {M : ℕ} (q : ℕ) (x : EdgeTuple V M) : ℕ :=
  (Finset.range M).sum (fun k => if Colorable q (tuplePrefix x (k + 1)) then 1 else 0)

def cappedCDF (q M m : ℕ) : ℝ :=
  uniformProb (fun x : EdgeTuple V M => cappedLast q x ≤ m)

def cappedTail (q M m : ℕ) : ℝ :=
  uniformProb (fun x : EdgeTuple V M => m ≤ cappedLast q x)

def lowerQuantile (q M : ℕ) (η : ℝ) : ℕ :=
  if h : ∃ m : ℕ, m ≤ M ∧ η ≤ cappedCDF (V := V) q M m then Nat.find h else M

/-- Search backwards from M to implement the maximum without an arbitrary choice. -/
def upperQuantile (q M : ℕ) (η : ℝ) : ℕ :=
  M - (if h : ∃ k : ℕ, k ≤ M ∧ η ≤ cappedTail (V := V) q M (M - k)
    then Nat.find h else M)

def quantileWindow (q M : ℕ) (η : ℝ) : ℝ :=
  (upperQuantile (V := V) q M η : ℝ) - (lowerQuantile (V := V) q M η : ℝ)

def clippedLast {M : ℕ} (q L U : ℕ) (x : EdgeTuple V M) : ℕ :=
  min U (max L (cappedLast q x))

def deletionY {U : ℕ} (q L : ℕ) (x : EdgeTuple V U) : ℕ :=
  L + ∑ m ∈ Finset.Icc (L + 1) U, if Colorable q (tuplePrefix x m) then 1 else 0

def deletionYMinus {U : ℕ} (q L : ℕ) (i : Fin U) (x : EdgeTuple V U) : ℕ :=
  L + ∑ m ∈ Finset.Icc (L + 1) U, if Colorable q (deletedPrefix x i m) then 1 else 0

end ThresholdFoundations

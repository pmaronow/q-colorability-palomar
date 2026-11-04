module

public import ThLean.Defs

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S4
open ThresholdFoundations

/-- The finite terminal functional, with actual failure time k+1 in (L,U]. -/
def terminalReal {V : Type} [Fintype V] (q L U : ℕ)
    (F : ℕ → MGraph V → Pair V → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico L U,
    uniformMean (fun x : EdgeTuple V k => uniformMean (fun e : Pair V =>
      if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
      then F (k+1) (tupleGraph x) e else 0))

/-- Finite terminal probability, never conditional on failure in the interval. -/
def terminalProb {V : Type} [Fintype V] (q L U : ℕ)
    (P : MGraph V → Pair V → Prop) : ℝ :=
  terminalReal q L U (fun _ G e => indicator (P G e))

/-- Sentinel T+1 means no failure by T. -/
def boundedFailure {V : Type} [Fintype V] {T : ℕ}
    (q : ℕ) (x : EdgeTuple V T) : ℕ := cappedLast q x + 1

def boundedLast {V : Type} [Fintype V] {T : ℕ}
    (q : ℕ) (x : EdgeTuple V T) : MGraph V :=
  tuplePrefix x (boundedFailure q x - 1)

/-- The final edge is evaluated only on a proved finite failure branch. -/
def terminalSample {V : Type} [Fintype V] {T : ℕ}
    (q L U : ℕ) (F : ℕ → MGraph V → Pair V → ℝ) (x : EdgeTuple V T) : ℝ :=
  if h : L < boundedFailure q x ∧ boundedFailure q x ≤ U ∧ U ≤ T then
    F (boundedFailure q x) (boundedLast q x)
      (x ⟨boundedFailure q x - 1, by have := h.1; have := h.2.1; have := h.2.2; omega⟩)
  else 0

/-- Prefix with the distinguished occurrence removed, keeping original order. -/
def omitBlock {E : Type} {T : ℕ} (x : Fin T → E) (i : Fin T)
    (m : ℕ) (hi : i.val < m) (hm : m ≤ T) : Fin (m-1) → E :=
  fun j => x ⟨if j.val < i.val then j.val else j.val+1, by
    have := j.isLt
    split_ifs <;> omega⟩

/-- The independent block at coordinates m,...,l-1. -/
def futureBlock {E : Type} {T : ℕ} (x : Fin T → E)
    (m l : ℕ) (hm : m ≤ l) (hl : l ≤ T) : Fin (l-m) → E :=
  fun j => x ⟨m+j.val, by have := j.isLt; omega⟩

/-- A finite terminal capped lifetime moment. -/
def cappedMoment (q n L U : ℕ) (a : ℝ) : ℝ :=
  terminalReal (V := Fin n) q L U (fun _ G _ => min a (lifetimeReal q G))

/-- The exact deletion terminal weight from eq:red-deletion. -/
def deletionMoment (q n L U : ℕ) : ℝ :=
  terminalReal (V := Fin n) q L U
    (fun h G _ => (h : ℝ)*(2*truncatedLifetime q (U+1-h) G-1))

end ThLean.BP.S4

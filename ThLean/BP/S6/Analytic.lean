module

public import ThLean.BP.S6.Potential

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S6

def fourthLog (n : ℕ) : ℝ := Real.rpow (Real.log (n : ℝ)) ((1 : ℝ) / 4)
def analyticCutoff (Λ : ℝ) : ℝ :=
  max 1 (max (2 * ((pivotalCut Λ : ℝ) + 1))
    (max (4 * Real.exp 1 ^ 2 * Λ + 2)
      (max (16 * (Nat.factorial 7 : ℝ) / (3 * Real.log 2 ^ 7))
        (24 * Real.exp 1 * Λ * 2 ^ 11 * (Nat.factorial 11 : ℝ) / Real.log 2))))
def sizeCutoff (Λ : ℝ) : ℕ := max 3 (Nat.ceil (Real.exp (analyticCutoff Λ ^ 4)))
def successCount {m : ℕ} (x : Fin m → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card
def bernoulliWeight {m : ℕ} (p : ℝ) (x : Fin m → Bool) : ℝ :=
  p ^ successCount x * (1 - p) ^ (m - successCount x)

/-- P4-HIGH-X01; one exponential-series term and its reciprocal consequence. Paper label: `lem:pre-tails(a)`; blueprint ID: `P4-HIGH-X01`. -/
def S6_X01Statement : Prop :=
  (∀ (t : ℝ) (k : ℕ), 0 ≤ t → t ^ k / (k.factorial : ℝ) ≤ Real.exp t) ∧
  (∀ (t : ℝ) (k : ℕ), 0 < t → Real.exp (-t) ≤ (k.factorial : ℝ) / t ^ k)

/-- P4-HIGH-X02; elementary factorial lower bound, pre-tails proof. Paper label: `lem:pre-tails(a)`; blueprint ID: `P4-HIGH-X02`. -/
def S6_X02Statement : Prop := ∀ k : ℕ, 1 ≤ k →
  ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ)

/-- P4-HIGH-X03; binomial coefficient bounds, pre-tails proof. Paper label: `lem:pre-tails(a)`; blueprint ID: `P4-HIGH-X03`. -/
def S6_X03Statement : Prop := ∀ m k : ℕ, 1 ≤ k →
  (m.choose k : ℝ) ≤ (m : ℝ) ^ k / (k.factorial : ℝ) ∧
  (m : ℝ) ^ k / (k.factorial : ℝ) ≤ (Real.exp 1 * m / k) ^ k

/-- P4-HIGH-X04; finite Bernoulli union tail, lem. pre-tails(a). Paper label: `lem:pre-tails(a)`; blueprint ID: `P4-HIGH-X04`. -/
def S6_X04Statement : Prop := ∀ (m k : ℕ) (p : ℝ),
  1 ≤ k → 0 ≤ p → p ≤ 1 →
  (∑ x : Fin m → Bool, bernoulliWeight p x * indicator (k ≤ successCount x)) =
    binomialTail m p k ∧
  binomialTail m p k ≤ (m.choose k : ℝ) * p ^ k ∧
  (m.choose k : ℝ) * p ^ k ≤ (Real.exp 1 * m * p / k) ^ k

/-- P4-HIGH-X05; numerical exponential bound used in high-params. Paper label: `eq:high-params`; blueprint ID: `P4-HIGH-X05`. -/
def S6_X05Statement : Prop := 1 < Real.exp 1 ∧ Real.exp 1 < 3

/-- Explicit parameter facts used by the descent and the cutoff. -/
structure ParameterFacts (n : ℕ) (Λ : ℝ) : Prop where
  cap_le : (cap Λ n : ℝ) ≤ Λ * n
  Kpos : 1 ≤ pivotalCut Λ
  Kge : 8 * Λ ≤ (pivotalCut Λ : ℝ)
  Dpos : 1 ≤ degreeCut n
  div_lower : 2 * descentCut n ≤ degreeCut n
  div_upper : degreeCut n ≤ 2 * descentCut n + 1
  wlt : descentCut n < degreeCut n
  D_lower : fourthLog n - 1 ≤ (degreeCut n : ℝ)
  w_lower : fourthLog n / 2 - 1 ≤ (descentCut n : ℝ)
  gap_lower : fourthLog n / 2 ≤ (degreeCut n + 1 - descentCut n : ℕ)
  root_pos : 0 < fourthLog n
  root_pow : fourthLog n ^ 4 = Real.log (n : ℝ)
  ratio_pos : 0 < (n : ℝ) / ((n : ℝ) - 1)
  ratio_sq : ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 ≤ 9 / 4
  contraction : ∀ m : ℕ, m ≤ cap Λ n → 2 * m / ((n : ℝ) * pivotalCut Λ) ≤ 1 / 4
  wpos : pivotalCut Λ ≤ descentCut n → 1 ≤ descentCut n
  denom : pivotalCut Λ ≤ descentCut n → 2 ≤ descentCut n - pivotalCut Λ + 2

/-- P4-HIGH-33; parameter and floor arithmetic, eq. high-params. Paper label: `eq:high-params`; blueprint ID: `P4-HIGH-33`. -/
def S6_33Statement : Prop := ∀ (n : ℕ) (Λ : ℝ), 3 ≤ n → 0 < Λ → ParameterFacts n Λ

/-- P4-HIGH-36; finite geometric bounds, high-descent lines 167--175. Paper label: `prop:high-descent`; blueprint ID: `P4-HIGH-36`. -/
def S6_36Statement : Prop := ∀ r L : ℕ,
  (∑ s ∈ Finset.range L, alpha ^ (r + s)) ≤ (4 / 3 : ℝ) * alpha ^ r ∧
  (∑ s ∈ Finset.range L, alpha ^ s) ≤ (4 / 3 : ℝ) ∧
  (∀ s : ℕ, 0 ≤ alpha ^ s)

/-- P4-HIGH-42; elementary two-term majorant, high-main lines 428--436. Paper label: `thm:high-main`; blueprint ID: `P4-HIGH-42`. -/
def S6_42Statement : Prop := ∀ (n : ℕ) (Λ : ℝ), 3 ≤ n → 0 < Λ →
  pivotalCut Λ ≤ descentCut n → 2 * Real.exp 1 ^ 2 * Λ ≤ (descentCut n : ℝ) →
    highBound Λ n ≤ (8 / 3 : ℝ) * Real.exp (-(Real.log 2) * fourthLog n) +
      (12 * Real.exp 1 * Λ / Real.log 2) * fourthLog n ^ 4 * Real.exp (-fourthLog n / 2)

/-- P4-HIGH-43; explicit analytic cutoff, quantitative form of high-main. Paper label: `thm:high-main`; blueprint ID: `P4-HIGH-43`. -/
def S6_43Statement : Prop := ∀ (n : ℕ) (Λ : ℝ), 3 ≤ n → 0 < Λ →
  analyticCutoff Λ ≤ fourthLog n →
    pivotalCut Λ ≤ descentCut n ∧
    2 * Real.exp 1 ^ 2 * Λ ≤ (descentCut n : ℝ) ∧
    highBound Λ n ≤ epsilon n

/-- P4-HIGH-44a; ceiling and logarithm bridge for the explicit size cutoff. Paper label: `thm:high-main`; blueprint ID: `P4-HIGH-44a`. -/
def S6_44aStatement : Prop := ∀ (n : ℕ) (Λ : ℝ), 0 < Λ → sizeCutoff Λ ≤ n →
  3 ≤ n ∧ analyticCutoff Λ ≤ fourthLog n

end ThLean.BP.S6

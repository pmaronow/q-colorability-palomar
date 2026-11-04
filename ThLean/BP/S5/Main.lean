module

public import ThLean.BP.S5.Occupation

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S5
open ThresholdFoundations

/-- P3-LOW-35; eq:low-conditions: a single cutoff works for every later n. -/
def S5_35Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → GoodSize q n

/-- P3-LOW-36; low-conditions: floor/ceiling ranges and positive logarithms. -/
def S5_36Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 16 ≤ n → lowSizeOnset q ≤ n - 1 →
    2 * q + 1 ≤ n ∧ 1 ≤ degreeCut n ∧ 4 * degreeCut n ≤ n - 1 ∧
    0 < Real.log n ∧ 0 < Real.log (Real.log n) ∧ 1 ≤ lowTruncation n ∧
    Real.log n / Real.log (Real.log n) ≤ (lowTruncation n : ℝ) ∧
    (lowTruncation n : ℝ) ≤ Real.log n / Real.log (Real.log n) + 1

/-- P3-LOW-37; low-advance-bound: bound the amplified short-list term. -/
def S5_37Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 16 ≤ n → lowSizeOnset q ≤ n - 1 →
    (degreeCut n : ℝ)^(lowTruncation n) ≤
      (n : ℝ)^(1 / 4 : ℝ) * (Real.log n)^(1 / 4 : ℝ) ∧
    (degreeCut n : ℝ)^2 ≤ (Real.log n)^(1 / 2 : ℝ)

/-- P3-LOW-38; low-advance-bound: long-list tail and the strict truncation test. -/
def S5_38Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 16 ≤ n → lowSizeOnset q ≤ n - 1 →
    Real.log (Real.exp 1 * lowMeanBound q * Real.log (Real.log n)) ≤
      (1 / 8 : ℝ) * Real.log (Real.log n) →
    let R := Real.exp 1 * degreeCut n * lowMeanBound q / lowTruncation n
    0 < R ∧ R ≤ Real.exp (-(5 / 8 : ℝ) * Real.log (Real.log n)) ∧
    Real.exp (-(5 / 8 : ℝ) * Real.log (Real.log n)) < 1 ∧
    Real.exp 1 * degreeCut n * lowMeanBound q < (lowTruncation n : ℝ) ∧
    ((n - 1 : ℕ) : ℝ) * R^(lowTruncation n) ≤ (n : ℝ)^(3 / 8 : ℝ)

/-- P3-LOW-39; eq:low-advance-bound: specialize the identification estimate. -/
def S5_39Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → GoodSize q n →
    identificationAdvance (V := Fin (n - 1)) q (degreeCut n) < ∞ ∧
    advanceReal q (n - 1) (degreeCut n) ≤
      2 * identificationConstant q * (n : ℝ)^(3 / 8 : ℝ)

theorem S5_39_assembly (h26 : S5_26Statement) (h36 : S5_36Statement)
    (h37 : S5_37Statement) (h38 : S5_38Statement) : S5_39Statement := by
  intro q n hq hg
  rcases hg with ⟨hn, hon, _, hlog, hsmall⟩
  have hr := h36 q n hq hn hon
  have ht := h38 q n hq hn hon hlog
  have hd : degreeCut n ≤ n - 1 := by omega
  have hi := h26 q (n - 1) (degreeCut n) (lowTruncation n)
    hq hon hr.2.1 hr.2.2.1 ht.2.2.2.1
  have hs := h37 q n hq hn hon
  have hc : 0 ≤ identificationConstant q := by
    unfold identificationConstant
    positivity
  refine ⟨hi.1, ?_⟩
  have hsum : (degreeCut n : ℝ)^(lowTruncation n) +
      ((n - 1 : ℕ) : ℝ) *
        (Real.exp 1 * degreeCut n * lowMeanBound q / lowTruncation n)^(lowTruncation n) +
      (degreeCut n : ℝ)^2 + 1 ≤ 2 * (n : ℝ)^(3 / 8 : ℝ) := by
    linarith [hs.1, hs.2, ht.2.2.2.2]
  calc
    _ ≤ identificationBound q (n - 1) (degreeCut n) (lowTruncation n) := hi.2.1.trans hi.2.2
    _ ≤ identificationConstant q * (2 * (n : ℝ)^(3 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hc
    _ = _ := by ring

/-- P3-LOW-40A; low-main: explicit positive constant and final scalar absorption. -/
def S5_40AStatement : Prop :=
  (∀ q : ℕ, 3 ≤ q → 0 < lowBoundConstant q) ∧
  (∀ q n : ℕ, 3 ≤ q → 16 ≤ n → ∀ y : ℝ, 0 < y →
    let c := (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
      Real.sqrt ((1 + lifetimeConstant q) / y)
    0 ≤ c ∧ c * (2 * identificationConstant q * (n : ℝ)^(3 / 8 : ℝ)) ≤
      lowBoundConstant q * y^(-(1 / 2 : ℝ)) * (n : ℝ)^(3 / 8 : ℝ))

/-- P3-LOW-40; thm:low-main with C = 8 C_q sqrt(1+A_q), uniformly in y. -/
def S5_40Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → 0 < lowBoundConstant q ∧
    ∃ n₀ : ℕ, 2 * q + 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ y : ℝ, 0 < y →
      lowTerminalProbability (V := Fin n) q (degreeCut n) y ≤
        lowBoundConstant q * y^(-(1 / 2 : ℝ)) * (n : ℝ)^(3 / 8 : ℝ)

theorem S5_40_assembly (h34 : S5_34Statement) (h35 : S5_35Statement)
    (h36 : S5_36Statement) (h39 : S5_39Statement) (ha : S5_40AStatement) :
    S5_40Statement := by
  intro q hq
  obtain ⟨N, hN⟩ := h35 q hq
  refine ⟨ha.1 q hq, max N (2 * q + 1), le_max_right _ _, ?_⟩
  intro n hn y hy
  have hg := hN n (le_trans (le_max_left _ _) hn)
  have hr := h36 q n hq hg.1 hg.2.1
  have hD : degreeCut n ≤ n - 1 := by omega
  have hi := h39 q n hq hg
  have hc := ha.2 q n hq hg.1 y hy
  calc
    _ ≤ (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
        Real.sqrt ((1 + lifetimeConstant q) / y) * advanceReal q (n - 1) (degreeCut n) :=
      h34 q n (degreeCut n) hq hr.1 hr.2.1 hD y hy
    _ ≤ (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
        Real.sqrt ((1 + lifetimeConstant q) / y) *
        (2 * identificationConstant q * (n : ℝ)^(3 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hi.2 hc.1
    _ ≤ _ := hc.2

/-- P3-LOW-41; low-cor: logarithms absorb the final polynomial saving. -/
def S5_41Statement : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n₁ : ℕ, 3 ≤ n₁ ∧ ∀ n : ℕ, n₁ ≤ n →
    0 < lifetimeCut n ∧ C * (Real.log n)^3 ≤ (n : ℝ)^(1 / 8 : ℝ) ∧
    C * (lifetimeCut n)^(-(1 / 2 : ℝ)) * (n : ℝ)^(3 / 8 : ℝ) =
      C * (Real.log n)^(3 / 2 : ℝ) * (n : ℝ)^(-(1 / 8 : ℝ)) ∧
    C * (lifetimeCut n)^(-(1 / 2 : ℝ)) * (n : ℝ)^(3 / 8 : ℝ) ≤ epsilon n

/-- P3-LOW-42A; red-low: every finite-window event is contained in the all-time event. -/
def S5_42AStatement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 2 * q ≤ n → ∀ y : ℝ, 0 < y → ∀ L U : ℕ,
    windowLow q n D y L U ≤ lowTerminalProbability (V := Fin n) q D y

/-- P3-LOW-42; cor:low and its uniform finite-window strengthening. -/
def S5_42Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ n₀ : ℕ, 2 * q + 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    lowTerminalProbability (V := Fin n) q (degreeCut n) (lifetimeCut n) ≤ epsilon n ∧
    (∀ L U : ℕ, L ≤ U →
      windowLow q n (degreeCut n) (lifetimeCut n) L U ≤ epsilon n)

theorem S5_42_assembly (h40 : S5_40Statement) (h41 : S5_41Statement)
    (ha : S5_42AStatement) : S5_42Statement := by
  intro q hq
  obtain ⟨hC, N, hN, hmain⟩ := h40 q hq
  obtain ⟨M, _, hsmall⟩ := h41 (lowBoundConstant q) hC
  refine ⟨max N M, le_trans hN (le_max_left _ _), ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M ≤ n := le_trans (le_max_right _ _) hn
  have hs := hsmall n hnM
  have hb := (hmain n hnN (lifetimeCut n) hs.1).trans hs.2.2.2
  refine ⟨hb, ?_⟩
  intro L U _
  exact (ha q n (degreeCut n) hq (by omega) (lifetimeCut n) hs.1 L U).trans hb

end ThLean.BP.S5

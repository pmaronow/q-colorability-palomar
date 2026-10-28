import ThLean.BP.S4.Objects

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S4
open ThresholdFoundations

/-- P2-PAR-01(a), positive logarithms and admissible parameters; eq:proof-params. -/
def S4_PAR_01AStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q →
    0 < Real.log (q : ℝ) ∧ 0 < Real.log ((q : ℝ)/((q : ℝ)-1)) ∧ 0 < gamma q ∧
    ∀ Λ : ℝ, gamma q+1 < Λ →
      1 < Λ ∧ 0 < etaZero Λ ∧ etaZero Λ < 1/2 ∧
      (∀ η : ℝ, 0 < η → η ≤ etaZero Λ → 1 ≤ 6*Λ/η^2 ∧ 0 < 6*Λ/η^2) ∧
      (∀ n : ℕ, (cap Λ n : ℝ) ≤ Λ*n)

/-- P2-PAR-01(b), the special choice of Lambda; eq:proof-params. -/
def S4_PAR_01BStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → gamma q+1 < capDensity q

/-- P2-PAR-01, constants and the integer cap. -/
def S4_PAR_01Statement : Prop := S4_PAR_01AStatement ∧ S4_PAR_01BStatement

theorem S4_PAR_01_assembly (ha : S4_PAR_01AStatement) (hb : S4_PAR_01BStatement) :
    S4_PAR_01Statement := ⟨ha,hb⟩

/-- P2-PAR-02, numerical log estimate used in Section 7. -/
def S4_PAR_02Statement : Prop := Real.exp 1 < 3 ∧ 1 < Real.log 3

/-- P2-PAR-03, total epsilon range and monotonicity; eq:proof-params. -/
def S4_PAR_03Statement : Prop :=
  (∀ n : ℕ, 0 < epsilon n ∧ epsilon n ≤ 1) ∧
  (∀ i j : ℕ, i ≤ j → epsilon j ≤ epsilon i)

/-- P2-PAR-04, floor on exponential scales; proof of thm:intro-main. -/
def S4_PAR_04Statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    3 ≤ Nat.floor (Real.exp (k : ℝ)) ∧
    Real.exp ((k : ℝ)-1) ≤ (Nat.floor (Real.exp (k : ℝ)) : ℝ) ∧
    epsilon (Nat.floor (Real.exp (k : ℝ))) ≤ Real.rpow ((k : ℝ)-1) (-(3 : ℝ)/2)

/-- P2-PAR-05, the sampled epsilon series; proof of thm:intro-main. -/
def S4_PAR_05Statement : Prop :=
  Summable (fun k : ℕ => epsilon (Nat.floor (Real.exp (k+1 : ℝ))))

/-- P2-PAR-06, vanishing error and absorption of the integer endpoint; thm:intro-window. -/
def S4_PAR_06Statement : Prop :=
  Tendsto epsilon atTop (𝓝 0) ∧
  Tendsto (fun n : ℕ => (n : ℝ)*epsilon n) atTop atTop ∧
  ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ (n : ℝ)*epsilon n

/-- P2-EXT-01, positive-index p-series (available in the pinned Mathlib). -/
def S4_EXT_01Statement : Prop :=
  ∀ s : ℝ, 1 < s → Summable (fun k : ℕ => Real.rpow (k+1 : ℝ) (-s))

theorem S4_EXT_01_assembly : S4_EXT_01Statement := by
  intro s hs
  have h : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h

/-- P2-EXT-02, exponential domination and its logarithmic consequence. -/
def S4_EXT_02Statement : Prop :=
  (∀ p a : ℝ, 0 < a →
    Tendsto (fun t : ℝ => Real.rpow t p * Real.exp (-a*t)) atTop (𝓝 0)) ∧
  (∀ s b : ℝ, 0 < b →
    Tendsto (fun x : ℝ => Real.rpow (Real.log x) s / Real.rpow x b) atTop (𝓝 0))

theorem S4_EXT_02_assembly : S4_EXT_02Statement := by
  constructor
  · intro p a ha
    exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p a ha
  · intro s b hb
    exact (isLittleO_log_rpow_rpow_atTop s hb).tendsto_div_nhds_zero

end ThLean.BP.S4

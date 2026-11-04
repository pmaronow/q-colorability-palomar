module

public import ThLean.BP.SA.Common

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.SA
open ThresholdFoundations

/-- P5-F01; parameter arithmetic, P:27--45 and A:3,182--193. Paper label: `lem:pre-centre`; blueprint: `P5-F01`. -/
def SA_F01Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q →
    0 < Real.log ((q : ℝ) / ((q : ℝ) - 1)) ∧ 1 ≤ gamma q ∧
    ∀ Λ : ℝ, gamma q + 1 < Λ →
      0 < Λ ∧ 0 < etaZero Λ ∧ etaZero Λ < (1 / 8 : ℝ) ∧ (1 / 8 : ℝ) < 1 / 2

/-- P5-F03; quantile comparison across levels, A:380--388. Paper label: `lem:pre-quantile`; blueprint: `P5-F03`. -/
def SA_F03Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    ∀ n : ℕ, 2 * q ≤ n → ∀ η₁ η₂ : ℝ, 0 < η₁ → η₁ ≤ η₂ → η₂ ≤ 1 / 2 →
      lowerLocation q Λ η₁ n ≤ lowerLocation q Λ η₂ n ∧
      lowerLocation q Λ η₂ n ≤ upperLocation q Λ η₁ n

/-- P5-F02: the upper-tail quantile bound beyond the cap, once U is below it. Paper label: `lem:pre-quantile`; blueprint: `P5-F02`. -/
def SA_F02Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ η : ℝ, gamma q + 1 < Λ → 0 < η → η ≤ 1 / 2 →
    ∀ n : ℕ, 2 * q ≤ n → upperLocation q Λ η n < cap Λ n →
    ∀ m : ℕ, upperLocation q Λ η n < m → processSurvival (V := Fin n) q m < η

/-- Finite probability bounds needed by all three model transfers. Paper label: `lem:conv-transfer`; blueprint: `P5-F02`. -/
def SA_F00Statement : Prop :=
  (∀ (A : Type) [Fintype A] [Nonempty A] (P : A → Prop),
    0 ≤ uniformProb P ∧ uniformProb P ≤ 1 ∧
      uniformProb (fun a => ¬ P a) = 1 - uniformProb P) ∧
  (∀ q n : ℕ, 1 ≤ q → 2 ≤ n → ∀ m : ℕ,
    0 ≤ processSurvival (V := Fin n) q m ∧ processSurvival (V := Fin n) q m ≤ 1) ∧
  (∀ q n m : ℕ, 1 ≤ q → 2 ≤ n → m ≤ n.choose 2 →
    0 ≤ simpleProbability (V := Fin n) q m ∧ simpleProbability (V := Fin n) q m ≤ 1) ∧
  (∀ q n : ℕ, 1 ≤ q → 2 ≤ n → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    0 ≤ bernoulliProbability (V := Fin n) q p ∧ bernoulliProbability (V := Fin n) q p ≤ 1)
end ThLean.BP.SA

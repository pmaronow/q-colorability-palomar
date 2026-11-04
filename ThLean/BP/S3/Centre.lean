module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `eq:pre-gamma,lem:pre-centre(a)`; blueprint P1-52. -/
def S3_52Statement : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    0 < Real.log ((q : ℝ)/((q : ℝ)-1)) ∧ 0 < Real.log (q : ℝ) ∧ 1 ≤ gamma q ∧
    (∀ (β : ℝ) (n : ℕ), gamma q < β → 2*q ≤ n →
      processSurvival (V := Fin n) q (Nat.floor (β*n)) ≤
        (((q : ℝ)/((q : ℝ)-1)) * Real.exp (2*β)) *
          Real.exp (-(n : ℝ)*(β-gamma q)*Real.log ((q : ℝ)/((q : ℝ)-1)))) ∧
    (∀ Λ : ℝ, gamma q + 1 < Λ → 2 < Λ ∧ 0 < etaZero Λ ∧ etaZero Λ < 1/2)

/-- Paper `lem:pre-centre(a)`; blueprint P1-53. -/
def S3_53Statement : Prop :=
  ∀ (q : ℕ) (Λ η β : ℝ), 3 ≤ q → gamma q+1 < Λ →
    0 < η → η ≤ 1/2 → gamma q < β →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 2*q ≤ n →
      lowerLocation q Λ η n ≤ upperLocation q Λ η n ∧
      upperLocation q Λ η n ≤ Nat.floor (β*n) ∧
      ((Nat.floor (β*n) : ℕ) : ℝ) ≤ β*n ∧
      upperLocation q Λ η n < cap Λ n

/-- Paper `lem:pre-poisson,lem:pre-lifetime(a)`; blueprint P1-54. -/
def S3_54Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2*q ≤ Fintype.card V →
    (∀ t : ℝ, 0 ≤ t →
      poissonGraphMean t (fun G : MGraph V => indicator (Colorable q G)) ≤
        min 1 ((q : ℝ)^(Fintype.card V) * Real.exp (-t/(2*q)))) ∧
    IntegrableOn (fun t : ℝ =>
      poissonGraphMean t (fun G : MGraph V => indicator (Colorable q G)))
      (Set.Ioi (2*q*Fintype.card V*Real.log q)) ∧
    (∫ t : ℝ in Set.Ioi (2*q*Fintype.card V*Real.log q),
      poissonGraphMean t (fun G : MGraph V => indicator (Colorable q G))) ≤ 2*q

/-- Paper `lem:pre-centre(b)`; blueprint P1-72. -/
def S3_72Statement : Prop :=
  (∀ a : ℝ, 0 ≤ a → a < 1 →
    Summable (fun j : ℕ => ((j+4 : ℕ) : ℝ)^2 * a^(j+3)) ∧
    obstructionSeries a = a^3*(16-23*a+9*a^2)/(1-a)^3) ∧
    obstructionSeries (1/2) = 27/4

/-- Paper `lem:pre-centre(b)`; blueprint P1-73. -/
def S3_73Statement : Prop :=
  ∀ (c : ℝ) (N m : ℕ), 0 < c → c < 1/2 → 2 ≤ N → (m : ℝ) ≤ c*N →
    (∀ k : ℕ, k ≤ N → ((N : ℝ)/((N : ℝ)-1))^k ≤ Real.exp 2) ∧
    (∑ k ∈ Finset.Icc 2 N, 2*((k+2 : ℕ) : ℝ)^2*(N : ℝ)^k *
      ((m : ℝ)/(N.choose 2 : ℝ))^(k+1)) ≤
        (2*Real.exp 2/((N : ℝ)-1)) * obstructionSeries (2*c) ∧
    (2*Real.exp 2/((N : ℝ)-1)) * obstructionSeries (2*c) ≤ obstructionConstant c/N ∧
    0 < obstructionConstant c

/-- Paper `lem:pre-centre(b)`; blueprint P1-74. -/
def S3_74Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
  ∀ (c : ℝ) (m : ℕ), 0 < c → c < 1/2 → (m : ℝ) ≤ c*Fintype.card V →
    1-processSurvival (V := V) q m ≤ obstructionConstant c / Fintype.card V

theorem S3_74_assembly (h71 : S3_71Statement.{u}) (h73 : S3_73Statement) :
    S3_74Statement.{u} := by
  intro V _ q hq hV c m hc0 hc1 hm
  have h := h73 c (Fintype.card V) m hc0 hc1 hV hm
  exact (h71 V q hq hV m).trans (h.2.1.trans h.2.2.1)

/-- Paper `lem:pre-centre(b)`; blueprint P1-75. -/
def S3_75Statement : Prop :=
  ∀ (q : ℕ) (Λ η c : ℝ), 3 ≤ q → gamma q+1 < Λ →
    0 < η → η ≤ 1/2 → 0 < c → c < 1/2 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 2*q ≤ n →
      c*n < (lowerLocation q Λ η n : ℝ)

/-- Paper `lem:pre-centre`; blueprint P1-76a. -/
def S3_76aStatement : Prop :=
  ∀ (q : ℕ) (Λ η : ℝ), 3 ≤ q → gamma q+1 < Λ → 0 < η → η ≤ 1/2 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 2*q ≤ n →
      (n : ℝ)/4 < lowerLocation q Λ η n ∧
      lowerLocation q Λ η n ≤ upperLocation q Λ η n ∧
      upperLocation q Λ η n < cap Λ n

theorem S3_76a_assembly (h53 : S3_53Statement) (h75 : S3_75Statement) :
    S3_76aStatement := by
  intro q Λ η hq hΛ hη0 hη1
  obtain ⟨N,hU⟩ := h53 q Λ η (gamma q+1) hq hΛ hη0 hη1 (by linarith)
  obtain ⟨M,hL⟩ := h75 q Λ η (1/4) hq hΛ hη0 hη1 (by norm_num) (by norm_num)
  refine ⟨max N M,?_⟩
  intro n hn hnq
  have hu := hU n (le_trans (le_max_left _ _) hn) hnq
  have hl := hL n (le_trans (le_max_right _ _) hn) hnq
  refine ⟨?_,hu.1,hu.2.2.2⟩
  nlinarith

/-- Paper `lem:pre-centre`; blueprint P1-76. -/
def S3_76Statement : Prop :=
  S3_52Statement ∧ S3_53Statement ∧ S3_74Statement.{u} ∧ S3_75Statement ∧ S3_76aStatement
theorem S3_76_assembly (h52 : S3_52Statement) (h53 : S3_53Statement)
    (h74 : S3_74Statement.{u}) (h75 : S3_75Statement) : S3_76Statement.{u} :=
  ⟨h52,h53,h74,h75,S3_76a_assembly h53 h75⟩


/-- The explicit quarter-density constant in P1-74 and lem:pre-centre(b). -/
theorem S3_74_quarter (h72 : S3_72Statement) (h74 : S3_74Statement.{u}) :
    ∀ (V : Type u) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
    ∀ m : ℕ, (m : ℝ) ≤ (Fintype.card V : ℝ)/4 →
      1-processSurvival (V := V) q m ≤ 27*Real.exp 2/Fintype.card V := by
  intro V _ q hq hV m hm
  have hc : obstructionConstant (1/4) = 27*Real.exp 2 := by
    unfold obstructionConstant
    rw [show (2 : ℝ)*(1/4) = 1/2 by norm_num,h72.2]
    ring
  have hm' : (m : ℝ) ≤ (1/4 : ℝ)*Fintype.card V := by linarith
  simpa only [hc] using h74 V q hq hV (1/4) m (by norm_num) (by norm_num) hm'

end ThLean.BP.S3

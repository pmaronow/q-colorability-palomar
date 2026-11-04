module

public import ThLean.BP.S5.Completion

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S5
open ThresholdFoundations

/-- P3-LOW-30; eq:low-root: count frozen pairs through low endpoints. -/
def S5_30Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V → ∀ D : ℕ,
    (∀ G : MGraph V, lowKappa q D G ≤
      (1 / ((Fintype.card V).choose 2 : ℝ)) *
        ∑ a : V, indicator (degree G a ≤ D) * (partnerCount q G a : ℝ)) ∧
    (∀ ν : PMF (MGraph V), invariantLaw ν → ∀ f : MGraph V → ℝ,
      relabelInvariant f → (∀ G, 0 ≤ f G ∧ f G ≤ 1) → ∀ a : V,
      Summable (fun G => (ν G).toReal * (lowKappa q D G * f G)) ∧
      Summable (fun G => (ν G).toReal *
        (indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) * f G)) ∧
      lawMean ν (fun G => lowKappa q D G * f G) ≤
        (2 / ((Fintype.card V : ℝ) - 1)) *
          lawMean ν (fun G => indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) * f G))

/-- P3-LOW-31; eq:low-classmass: use the lifetime restriction only at the original graph. -/
def S5_31Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 * q ≤ Fintype.card V →
  ∀ (D : ℕ) (y : ℝ), 0 < y → ∀ ν : PMF (MGraph V), invariantLaw ν → ∀ a : V,
    Summable (fun G => (ν G).toReal * lowObservable q D y G) ∧
    Summable (fun G => (ν G).toReal * indicator (rootEvent q D a G)) ∧
    lawMean ν (lowObservable q D y) ≤
      (2 * Fintype.card V / ((Fintype.card V : ℝ) - 1)) *
        Real.sqrt ((1 + lifetimeConstant q) / y) *
          lawMean ν (fun G => indicator (rootEvent q D a G))

/-- P3-LOW-32; eq:low-nm: a short frozen root forces a random-list obstruction. -/
def S5_32Statement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 3 ≤ n → ∀ a : Fin n, ∀ t : ℝ, 0 ≤ t →
    rootProbability q D a t ≤
      (∑ j ∈ Finset.range (D + 1), poissonWeight (2 * t / n) j *
        nmTime q (n - 1) j ((((n : ℝ) - 2) / n) * t)) ∧
    (∑ j ∈ Finset.range (D + 1), poissonWeight (2 * t / n) j *
        nmTime q (n - 1) j ((((n : ℝ) - 2) / n) * t)) ≤
      nmTime q (n - 1) D ((((n : ℝ) - 2) / n) * t)

/-- P3-LOW-33A; eq:low-to-identify: finite NM occupation and its scaled sum. -/
def S5_33AStatement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 2 * q + 1 ≤ n → 1 ≤ D → D ≤ n - 1 →
    identificationAdvance (V := Fin (n - 1)) q D < ∞ ∧
    Summable (fun m => uniformMean (fun x : EdgeTuple (Fin (n - 1)) m =>
      nmProbability q D (tupleGraph x))) ∧
    IntegrableOn (fun t => nmTime q (n - 1) D ((((n : ℝ) - 2) / n) * t)) (Set.Ici 0) ∧
    (∫ t in Set.Ici (0 : ℝ), nmTime q (n - 1) D ((((n : ℝ) - 2) / n) * t)) =
      (n / ((n : ℝ) - 2)) * ∑' m, uniformMean
        (fun x : EdgeTuple (Fin (n - 1)) m => nmProbability q D (tupleGraph x)) ∧
    (∫ t in Set.Ici (0 : ℝ), nmTime q (n - 1) D ((((n : ℝ) - 2) / n) * t)) ≤
      (n / ((n : ℝ) - 2)) * advanceReal q (n - 1) D

/-- P3-LOW-33B; eq:low-to-identify: integrate the pointwise root domination. -/
def S5_33BStatement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 2 * q + 1 ≤ n → 1 ≤ D → D ≤ n - 1 → ∀ a : Fin n,
    IntegrableOn (rootProbability q D a) (Set.Ici 0) ∧
    (∫ t in Set.Ici (0 : ℝ), rootProbability q D a t) ≤
      (∫ t in Set.Ici (0 : ℝ), nmTime q (n - 1) D ((((n : ℝ) - 2) / n) * t))

/-- P3-LOW-33; eq:low-to-identify: root occupation is controlled by advance. -/
def S5_33Statement : Prop :=
  S5_33AStatement ∧
  (∀ q n D : ℕ, 3 ≤ q → 2 * q + 1 ≤ n → 1 ≤ D → D ≤ n - 1 → ∀ a : Fin n,
    IntegrableOn (rootProbability q D a) (Set.Ici 0) ∧
    (∫ t in Set.Ici (0 : ℝ), rootProbability q D a t) ≤
      (n / ((n : ℝ) - 2)) * advanceReal q (n - 1) D)

theorem S5_33_assembly (ha : S5_33AStatement) (hb : S5_33BStatement) :
    S5_33Statement := by
  refine ⟨ha, ?_⟩
  intro q n D hq hn hD hDn a
  exact ⟨(hb q n D hq hn hD hDn a).1,
    (hb q n D hq hn hD hDn a).2.trans (ha q n D hq hn hD hDn).2.2.2.2⟩

/-- P3-LOW-34A; eq:low-step1: terminal disintegration, with summability and integrability. -/
def S5_34AStatement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 2 * q + 1 ≤ n → ∀ y : ℝ, 0 < y →
    Summable (fun m => uniformMean (fun x : EdgeTuple (Fin n) m =>
      lowObservable q D y (tupleGraph x))) ∧
    lowTerminalProbability (V := Fin n) q D y =
      ∑' m, uniformMean (fun x : EdgeTuple (Fin n) m => lowObservable q D y (tupleGraph x)) ∧
    IntegrableOn (lowTime q n D y) (Set.Ici 0) ∧
    lowTerminalProbability (V := Fin n) q D y = ∫ t in Set.Ici (0 : ℝ), lowTime q n D y t

/-- P3-LOW-34B; eq:low-classmass: integrated comparison with one root. -/
def S5_34BStatement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 2 * q + 1 ≤ n → 1 ≤ D → D ≤ n - 1 →
  ∀ (y : ℝ), 0 < y → ∀ a : Fin n,
    (∫ t in Set.Ici (0 : ℝ), lowTime q n D y t) ≤
      (2 * n / ((n : ℝ) - 1)) * Real.sqrt ((1 + lifetimeConstant q) / y) *
        (∫ t in Set.Ici (0 : ℝ), rootProbability q D a t)

/-- P3-LOW-34; low-step1 through low-to-identify: finite-parameter bound. -/
def S5_34Statement : Prop :=
  ∀ q n D : ℕ, 3 ≤ q → 2 * q + 1 ≤ n → 1 ≤ D → D ≤ n - 1 →
  ∀ y : ℝ, 0 < y →
    lowTerminalProbability (V := Fin n) q D y ≤
      (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
        Real.sqrt ((1 + lifetimeConstant q) / y) * advanceReal q (n - 1) D

theorem S5_34_assembly (ha : S5_34AStatement) (hb : S5_34BStatement)
    (h33 : S5_33Statement) : S5_34Statement := by
  intro q n D hq hn hD hDn y hy
  let a : Fin n := ⟨0, by omega⟩
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hcoef : 0 ≤ (2 * n / ((n : ℝ) - 1)) * Real.sqrt ((1 + lifetimeConstant q) / y) := by
    apply mul_nonneg
    · exact div_nonneg (by positivity) (by linarith)
    · exact Real.sqrt_nonneg _
  rw [(ha q n D hq hn y hy).2.2.2]
  calc
    _ ≤ (2 * n / ((n : ℝ) - 1)) * Real.sqrt ((1 + lifetimeConstant q) / y) *
        (∫ t in Set.Ici (0 : ℝ), rootProbability q D a t) := hb q n D hq hn hD hDn y hy a
    _ ≤ (2 * n / ((n : ℝ) - 1)) * Real.sqrt ((1 + lifetimeConstant q) / y) *
        ((n / ((n : ℝ) - 2)) * advanceReal q (n - 1) D) :=
      mul_le_mul_of_nonneg_left (h33.2 q n D hq hn hD hDn a).2 hcoef
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end ThLean.BP.S5

module

public import ThLean.BP.S3.Graph
public import ThLean.BP.S3.Process

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `def:pre-lifetime`; blueprint P1-21. -/
def S3_21Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  (∀ (G : MGraph V) (ω : EdgeStream V) (k : ℕ),
    ((k : WithTop ℕ) < freshHittingTime q G ω ↔ Colorable q (G + processGraph ω k))) ∧
  (∀ (G : MGraph V) (b : ℕ),
    truncatedLifetime q b G = uniformMean (fun x : EdgeTuple V b =>
      ∑ k ∈ Finset.range b, indicator (Colorable q (G + tuplePrefix x k)))) ∧
  (∀ G : MGraph V, ¬ Colorable q G →
    lifetime q G = 0 ∧ (∀ b, truncatedLifetime q b G = 0) ∧
    (∀ ω, freshHittingTime q G ω = 0)) ∧
  (∀ (G : MGraph V) (b : ℕ),
    0 ≤ truncatedLifetime q b G ∧ truncatedLifetime q b G ≤ b ∧
    ENNReal.ofReal (truncatedLifetime q b G) ≤ lifetime q G) ∧
  (∀ G : MGraph V, Colorable q G →
    (∀ b : ℕ, 1 ≤ b → 1 ≤ truncatedLifetime q b G) ∧
    (1 : ℝ≥0∞) ≤ lifetime q G) ∧
  (∀ G : MGraph V, Monotone (fun b => truncatedLifetime q b G) ∧
    truncatedLifetime q 0 G = 0)

/-- Paper `lem:pre-lifetime(b)`; blueprint P1-22. -/
def S3_22Statement : Prop :=
  ∀ (V : Type u) (W : Type v) [Fintype V] [Fintype W] (q : ℕ), 2 ≤ q →
  2 ≤ Fintype.card V → 2 ≤ Fintype.card W →
  (∀ G H : MGraph V, subgraph G H →
    (∀ ω, freshHittingTime q H ω ≤ freshHittingTime q G ω) ∧
    lifetime q H ≤ lifetime q G ∧
    (∀ b, truncatedLifetime q b H ≤ truncatedLifetime q b G)) ∧
  (∀ (G : MGraph V) (π : V ≃ W), lifetime q (relabel π G) = lifetime q G ∧
    lifetimeReal q (relabel π G) = lifetimeReal q G ∧
    (∀ b, truncatedLifetime q b (relabel π G) = truncatedLifetime q b G))

/-- Paper `eq:pre-union`; blueprint P1-23. -/
def S3_23Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  ∀ σ : V → Fin q,
    (Fintype.card V : ℝ)^2 / q ≤ ∑ i : Fin q, (colorClassSize σ i : ℝ)^2 ∧
    ((Fintype.card V : ℝ) / q - 1) / ((Fintype.card V : ℝ)-1) ≤ monoPairProb σ ∧
    (2*q ≤ Fintype.card V → 1/(2*(q : ℝ)) ≤ monoPairProb σ) ∧
    1 - monoPairProb σ ≤ (((q : ℝ)-1)/q) *
      ((Fintype.card V : ℝ) / ((Fintype.card V : ℝ)-1))

/-- Paper `eq:pre-union,lem:pre-lifetime(a)`; blueprint P1-24. -/
def S3_24Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  ∀ (G : MGraph V) (k : ℕ),
    survival q G k ≤ (q : ℝ)^(Fintype.card V) *
      ((((q : ℝ)-1)/q) * ((Fintype.card V : ℝ) / ((Fintype.card V : ℝ)-1)))^k ∧
    (2*q ≤ Fintype.card V → survival q G k ≤
      min 1 ((q : ℝ)^(Fintype.card V) * Real.exp (-(k : ℝ)/(2*q)))) ∧
    (2*q ≤ Fintype.card V → survival q G k ≤
      (q : ℝ)^(Fintype.card V) * (1-1/(2*(q : ℝ)))^k)

/-- Paper `lem:pre-lifetime(a)`; blueprint P1-25. -/
def S3_25Statement : Prop :=
  ∀ B a : ℝ, 1 ≤ B → 0 < a →
    Summable (fun k : ℕ => min 1 (B * Real.exp (-a*k))) ∧
    (∑' k : ℕ, min 1 (B * Real.exp (-a*k))) ≤ Real.log B / a + 2 + 1/a ∧
    Summable (fun k : ℕ => Real.exp (-a*k)) ∧
    (∑' k : ℕ, Real.exp (-a*k)) = 1/(1-Real.exp (-a)) ∧
    1/(1-Real.exp (-a)) ≤ 1+1/a

/-- Paper `lem:pre-lifetime(a,d)`; blueprint P1-26. -/
def S3_26Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2*q ≤ Fintype.card V →
  0 < lifetimeConstant q ∧
  (∀ G : MGraph V, lifetime q G ≠ ⊤ ∧
    0 ≤ lifetimeReal q G ∧
    lifetimeReal q G ≤ 2*q*Fintype.card V*Real.log q + 2*q+2 ∧
    lifetimeReal q G ≤ lifetimeConstant q * Fintype.card V) ∧
  infiniteHittingProbability (V := V) q = 0 ∧
  Summable (processSurvival (V := V) q) ∧
  (∑' m : ℕ, processSurvival (V := V) q m) = lifetimeReal q (0 : MGraph V)

/-- Paper `lem:pre-lifetime(c)`; blueprint P1-27. -/
def S3_27Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2 ≤ Fintype.card V →
  (∀ G : MGraph V, 0 < kappa q G →
    (∀ k, survival q G k ≤ (1-kappa q G)^k) ∧ lifetime q G ≠ ⊤ ∧
    lifetimeReal q G ≤ 1 / kappa q G) ∧
  (2*q ≤ Fintype.card V → ∀ G : MGraph V, kappa q G * lifetimeReal q G ≤ 1)

/-- Paper `lem:pre-lifetime(d),eq:pre-r-conditional`; blueprint P1-28. -/
def S3_28Statement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2*q ≤ Fintype.card V →
  ∀ (m : ℕ) (z : EdgeTuple V m → ℝ), (∀ x, 0 ≤ z x) →
    let a := fun k : ℕ => uniformMean (fun x : EdgeTuple V (m+k) =>
      z (fun i => x (Fin.castAdd k i)) * indicator (Colorable q (tupleGraph x)))
    Summable a ∧ (∑' k, a k) = uniformMean (fun x : EdgeTuple V m =>
      z x * lifetimeReal q (tupleGraph x))

/-- Paper `lem:pre-lifetime`; blueprint P1-29. -/
def S3_29Statement : Prop :=
  S3_21Statement.{u} ∧ S3_22Statement.{u, v} ∧ S3_26Statement.{u} ∧ S3_27Statement.{u} ∧ S3_28Statement.{u}
theorem S3_29_assembly (h21 : S3_21Statement.{u}) (h22 : S3_22Statement.{u, v})
    (h26 : S3_26Statement.{u}) (h27 : S3_27Statement.{u}) (h28 : S3_28Statement.{u}) :
    S3_29Statement.{u, v} := ⟨h21,h22,h26,h27,h28⟩

/-- Paper `lem:pre-classmass`; blueprint P1-30a. -/
def S3_30aStatement : Prop :=
  ∀ (N A κ Q r : ℝ), 2 ≤ N → 0 ≤ A → 0 ≤ κ →
    1 ≤ r → r ≤ A*N → κ*r ≤ 1 → Q = (1-1/N)*κ+1/N →
    Q*r ≤ 1+A ∧ ∀ y : ℝ, 0 < y → y < r →
      Q ≤ (1+A)/r ∧ (1+A)/r < (1+A)/y ∧
      Real.sqrt Q ≤ Real.sqrt ((1+A)/y)

/-- Paper `lem:pre-classmass`; blueprint P1-30b. -/
def S3_30bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (q : ℕ), 2 ≤ q → 2*q ≤ Fintype.card V →
  ∀ G : MGraph V, Colorable q G →
    1 ≤ lifetimeReal q G ∧ lifetimeReal q G ≤ lifetimeConstant q * Fintype.card V ∧
    classMass q G * lifetimeReal q G ≤ 1+lifetimeConstant q ∧
    ∀ y : ℝ, 0 < y → y < lifetimeReal q G →
      classMass q G ≤ (1+lifetimeConstant q)/lifetimeReal q G ∧
      classMass q G < (1+lifetimeConstant q)/y ∧
      ∀ C ∈ frozenClasses q G,
        (C.card : ℝ) ≤ Fintype.card V * Real.sqrt ((1+lifetimeConstant q)/y)


theorem S3_30b_assembly (h9 : S3_09bStatement.{u, u}) (h11 : S3_11Statement.{u})
    (h12 : S3_12Statement.{u}) (h21 : S3_21Statement.{u}) (h26 : S3_26Statement.{u})
    (h27 : S3_27Statement.{u}) (ha : S3_30aStatement) : S3_30bStatement.{u} := by
  intro V _ q hq hV G hG
  have hn : 2 ≤ Fintype.card V := by omega
  have hnR : 2 ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hfinite := ((h26 V q hq hV).2.1 G).1
  have hr : 1 ≤ lifetimeReal q G := by
    have h := ((h21 V q hq hn).2.2.2.2.1 G hG).2
    simpa only [lifetimeReal, ENNReal.toReal_one] using ENNReal.toReal_mono hfinite h
  have hupper := ((h26 V q hq hV).2.1 G).2.2.2
  have hid : classMass q G =
      (1 - 1/(Fintype.card V : ℝ))*kappa q G + 1/Fintype.card V := by
    simpa [indicator, hG] using (h11 V q hq hn).2 G
  have halg := ha (Fintype.card V) (lifetimeConstant q) (kappa q G)
    (classMass q G) (lifetimeReal q G) hnR (h26 V q hq hV).1.le
    ((h9 V V q hq).2.2.2 G).1 hr hupper ((h27 V q hq hn).2 hV G) hid
  refine ⟨hr,hupper,halg.1,?_⟩
  intro y hy hyr
  obtain ⟨hqr,hstrict,hsqrt⟩ := halg.2 y hy hyr
  refine ⟨hqr,hqr.trans_lt hstrict,?_⟩
  intro C hC
  exact ((h12 V q hq hn).1 G C hC).2.trans
    (mul_le_mul_of_nonneg_left hsqrt (by positivity))

/-- Paper `lem:pre-classmass`; blueprint P1-30. -/
def S3_30Statement : Prop := S3_30bStatement.{u}
theorem S3_30_assembly (h : S3_30bStatement.{u}) : S3_30Statement.{u} := h

end ThLean.BP.S3

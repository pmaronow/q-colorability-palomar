import ThLean.BP.S5.Poisson

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S5
open ThresholdFoundations

/-- P3-LOW-17A; eq:low-advance: the pathwise discrepancy interval, at finite H. -/
def S5_17AStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q →
  ∀ Z : Finset V, Z.Nonempty → ∀ ω : EdgeStream V,
    identifiedHittingTime q Z ω ≤ hittingTime q ω ∧
    (∀ H : ℕ, hittingTime q ω = H →
      ∃ K : ℕ, identifiedHittingTime q Z ω = K ∧ K ≤ H ∧
        ((H - K : ℕ) : ℝ≥0∞) = ∑' m : ℕ,
          if Colorable q (processGraph ω m) ∧
            ¬ Colorable q (identify (processGraph ω m) Z) then 1 else 0)

/-- P3-LOW-17B; eq:low-advance: finite advance and its real series. -/
def S5_17BStatement : Prop :=
  ∀ q N D : ℕ, 3 ≤ q → 2 * q ≤ N → 1 ≤ D → D ≤ N →
    infiniteHittingProbability (V := Fin N) q = 0 ∧
    identificationAdvance (V := Fin N) q D < ∞ ∧
    0 ≤ advanceReal q N D ∧ advanceReal q N D ≤ lifetimeConstant q * N ∧
    HasSum (fun m => uniformMean (fun x : EdgeTuple (Fin N) m =>
      identificationFailureProbability q D (tupleGraph x))) (advanceReal q N D)

/-- P3-LOW-17C; eq:low-integral: integrable occupation representation. -/
def S5_17CStatement : Prop :=
  ∀ q N D : ℕ, 3 ≤ q → 2 * q ≤ N → 1 ≤ D → D ≤ N →
    IntegrableOn (discrepancy q N D) (Set.Ici 0) ∧
    (∫ s in Set.Ici (0 : ℝ), discrepancy q N D s) = advanceReal q N D

/-- P3-LOW-17 helper; eq:low-advance: generic finite vertex carrier bound. -/
def S5_17DStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 * q ≤ Fintype.card V →
  ∀ D : ℕ, 1 ≤ D → D ≤ Fintype.card V →
    identificationAdvance (V := V) q D ≤
      ENNReal.ofReal (lifetimeConstant q * Fintype.card V)

/-- P3-LOW-17; eq:low-advance and eq:low-integral. -/
def S5_17Statement : Prop := S5_17AStatement ∧ S5_17BStatement ∧ S5_17CStatement

theorem S5_17_assembly (ha : S5_17AStatement) (hb : S5_17BStatement)
    (hc : S5_17CStatement) : S5_17Statement := ⟨ha, hb, hc⟩

/-- P3-LOW-18; low-large: monochromatic pair fraction and first-moment bound. -/
def S5_18Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 * q ≤ Fintype.card V →
    (∀ σ : V → Fin q,
      1 / (2 * (q : ℝ)) ≤ uniformProb (fun e : Pair V =>
        ∃ u v, e.val = s(u, v) ∧ σ u = σ v)) ∧
    (∀ m : ℕ, processSurvival (V := V) q m ≤
      (q : ℝ)^(Fintype.card V) * (1 - 1 / (2 * (q : ℝ)))^m)

/-- P3-LOW-19; eq:low-large: late-time contribution at most 2q. -/
def S5_19Statement : Prop :=
  ∀ q N D : ℕ, 3 ≤ q → 2 * q ≤ N → 1 ≤ D → D ≤ N →
    (∀ s : ℝ, 0 ≤ s →
      0 ≤ discrepancy q N D s ∧
      discrepancy q N D s ≤ poissonGraphMean s
        (fun G : MGraph (Fin N) => indicator (Colorable q G)) ∧
      poissonGraphMean s (fun G : MGraph (Fin N) => indicator (Colorable q G)) ≤
        (q : ℝ)^N * Real.exp (-s / (2 * q))) ∧
    IntegrableOn (fun s : ℝ => (q : ℝ)^N * Real.exp (-s / (2 * q)))
      (Set.Ici (lowTimeCap q N)) ∧
    IntegrableOn (discrepancy q N D) (Set.Ici (lowTimeCap q N)) ∧
    (∫ s in Set.Ici (lowTimeCap q N), discrepancy q N D s) ≤ 2 * q

/-- P3-LOW-20; eq:low-split: a fixed identification and its internal-pair error. -/
def S5_20Statement : Prop :=
  ∀ q N : ℕ, 3 ≤ q → 3 ≤ N → ∀ Z : Finset (Fin N), Z.Nonempty →
  2 ≤ N - Z.card →
    (∀ s : ℝ, 0 ≤ s →
      poissonGraphMean s (fun G : MGraph (Fin N) =>
        indicator (Colorable q G ∧ ¬ Colorable q (identify G Z))) ≤
      lowEdgeRate N * (Z.card.choose 2 : ℝ) * s +
        addedFailure (V := {v : Fin N // v ∉ Z}) q
          (lowEdgeRate N * s) (Z.card * neighborMean N Z.card s)) ∧
    Measurable (fun s : Set.Ici (0 : ℝ) =>
      poissonGraphMean s.val (fun G : MGraph (Fin N) =>
        indicator (Colorable q G ∧ ¬ Colorable q (identify G Z)))) ∧
    Measurable (fun s : Set.Ici (0 : ℝ) =>
      addedFailure (V := {v : Fin N // v ∉ Z}) q
        (lowEdgeRate N * s.val) (Z.card * neighborMean N Z.card s.val))

/-- P3-LOW-21; eq:low-tilt: keep j≤k, discard precisely j>k. -/
def S5_21Statement : Prop :=
  ∀ D k : ℕ, 1 ≤ D → ∀ z : ℝ, 0 ≤ z →
    (∀ j : ℕ, j ≤ k →
      poissonWeight (D * z) j =
        (D : ℝ)^j * Real.exp (-((D : ℝ) - 1) * z) * poissonWeight z j ∧
      poissonWeight (D * z) j ≤ (D : ℝ)^k * poissonWeight z j) ∧
    (∀ b : ℕ → ℝ, (∀ j, 0 ≤ b j ∧ b j ≤ 1) →
      Summable (fun j => poissonWeight (D * z) j * b j) ∧
      Summable (fun j => poissonWeight z j * b j) ∧
      poissonMixture (D * z) b ≤ (D : ℝ)^k * poissonMixture z b +
        ∑' j : ℕ, if k < j then poissonWeight (D * z) j else 0)

/-- P3-LOW-22; low-constants/low-zeta: size, rate, and mean bounds. -/
def S5_22Statement : Prop :=
  ∀ q N D : ℕ, 3 ≤ q → lowSizeOnset q ≤ N → 1 ≤ D → 4 * D ≤ N →
    2 * q < lowSizeOnset q ∧ 2 * q < N ∧ D ≤ N ∧ 2 ≤ N - D ∧
    0 < lowEdgeRate N ∧ 0 < augmentedRate N D ∧ 0 < lowTimeCap q N ∧
    1 / augmentedRate N D =
      ((N : ℝ) * ((N : ℝ) - 1)) / (((N - D : ℕ) : ℝ) * ((N - D : ℕ) + 1)) ∧
    1 / augmentedRate N D ≤ (16 / 9 : ℝ) ∧ (16 / 9 : ℝ) < 2 ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ lowTimeCap q N →
      0 ≤ neighborMean N D s ∧ neighborMean N D s ≤ lowMeanBound q)

/-- P3-LOW-23; eq:low-inside: internal-pair integral with its exact coefficient. -/
def S5_23Statement : Prop :=
  ∀ q N D : ℕ, 3 ≤ q → 2 ≤ N → 1 ≤ D → D ≤ N →
    (∫ s in (0 : ℝ)..lowTimeCap q N, lowEdgeRate N * (D.choose 2 : ℝ) * s) =
      (D : ℝ) * ((D : ℝ) - 1) * (lowTimeCap q N)^2 /
        (2 * N * ((N : ℝ) - 1)) ∧
    (D : ℝ) * ((D : ℝ) - 1) * (lowTimeCap q N)^2 /
        (2 * N * ((N : ℝ) - 1)) =
      2 * (q : ℝ)^2 * (Real.log q)^2 *
        (D : ℝ) * ((D : ℝ) - 1) * N / ((N : ℝ) - 1) ∧
    (∫ s in (0 : ℝ)..lowTimeCap q N, lowEdgeRate N * (D.choose 2 : ℝ) * s) ≤
      2 * (q : ℝ)^2 * (Real.log q)^2 * (D : ℝ)^2

/-- P3-LOW-24; eq:low-tail: integrated long-list tail. -/
def S5_24Statement : Prop :=
  ∀ q N D k : ℕ, 3 ≤ q → lowSizeOnset q ≤ N → 1 ≤ D → 4 * D ≤ N →
  Real.exp 1 * D * lowMeanBound q < (k : ℝ) →
    1 ≤ k ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ lowTimeCap q N →
      (∑' j : ℕ, if k < j then poissonWeight (D * neighborMean N D s) j else 0) ≤
        (Real.exp 1 * D * lowMeanBound q / k)^k) ∧
    IntegrableOn (fun s : ℝ =>
      ∑' j : ℕ, if k < j then poissonWeight (D * neighborMean N D s) j else 0)
      (Set.Icc 0 (lowTimeCap q N)) ∧
    (∫ s in (0 : ℝ)..lowTimeCap q N,
      ∑' j : ℕ, if k < j then poissonWeight (D * neighborMean N D s) j else 0) ≤
      lowTimeCap q N * (Real.exp 1 * D * lowMeanBound q / k)^k

/-- P3-LOW-25; eq:low-main-term: integrate the ordinary-root comparison. -/
def S5_25Statement : Prop :=
  ∀ q N D k : ℕ, 3 ≤ q → lowSizeOnset q ≤ N → 1 ≤ D → 4 * D ≤ N →
  ∀ Z : UniformSubset (Fin N) D,
    IntegrableOn (fun s : ℝ => (D : ℝ)^k *
      addedFailure (V := {v : Fin N // v ∉ Z.val}) q
        (lowEdgeRate N * s) (neighborMean N D s)) (Set.Icc 0 (lowTimeCap q N)) ∧
    (∫ s in (0 : ℝ)..lowTimeCap q N, (D : ℝ)^k *
      addedFailure (V := {v : Fin N // v ∉ Z.val}) q
        (lowEdgeRate N * s) (neighborMean N D s)) ≤
      (D : ℝ)^k * (Real.exp (lowMeanBound q) - 1) / augmentedRate N D ∧
    (D : ℝ)^k * (Real.exp (lowMeanBound q) - 1) / augmentedRate N D ≤
      2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ)^k

/-- P3-LOW-26A; low-split/low-tilt: average and integrate the early-time estimate. -/
def S5_26AStatement : Prop :=
  ∀ q N D k : ℕ, 3 ≤ q → lowSizeOnset q ≤ N → 1 ≤ D → 4 * D ≤ N →
  Real.exp 1 * D * lowMeanBound q < (k : ℝ) →
    (∫ s in (0 : ℝ)..lowTimeCap q N, discrepancy q N D s) ≤
      2 * (q : ℝ)^2 * (Real.log q)^2 * (D : ℝ)^2 +
      lowTimeCap q N * (Real.exp 1 * D * lowMeanBound q / k)^k +
      2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ)^k

/-- P3-LOW-26B; low-identify: absorb all four coefficients into C_q. -/
def S5_26BStatement : Prop :=
  ∀ q N D k : ℕ, 3 ≤ q →
    rawIdentificationBound q N D k ≤ identificationBound q N D k

/-- P3-LOW-26C; low-integral: split the finite occupation at s_0. -/
def S5_26CStatement : Prop :=
  ∀ q N D : ℕ, 3 ≤ q → 2 * q ≤ N → 1 ≤ D → D ≤ N →
    identificationAdvance (V := Fin N) q D < ∞ ∧
    advanceReal q N D =
      (∫ s in (0 : ℝ)..lowTimeCap q N, discrepancy q N D s) +
      (∫ s in Set.Ici (lowTimeCap q N), discrepancy q N D s)

/-- P3-LOW-26; prop:low-identify, retaining the unabsorbed bound. -/
def S5_26Statement : Prop :=
  ∀ q N D k : ℕ, 3 ≤ q → lowSizeOnset q ≤ N → 1 ≤ D → 4 * D ≤ N →
  Real.exp 1 * D * lowMeanBound q < (k : ℝ) →
    identificationAdvance (V := Fin N) q D < ∞ ∧
    advanceReal q N D ≤ rawIdentificationBound q N D k ∧
    rawIdentificationBound q N D k ≤ identificationBound q N D k

theorem S5_26_assembly (h19 : S5_19Statement) (h22 : S5_22Statement)
    (ha : S5_26AStatement) (hb : S5_26BStatement) (hc : S5_26CStatement) :
    S5_26Statement := by
  intro q N D k hq hN hD h4 hk
  have hp := h22 q N D hq hN hD h4
  have hNq : 2 * q ≤ N := Nat.le_of_lt hp.2.1
  have hDN : D ≤ N := hp.2.2.1
  have hs := hc q N D hq hNq hD hDN
  refine ⟨hs.1, ?_, hb q N D k hq⟩
  have hearly := ha q N D k hq hN hD h4 hk
  have hlate := (h19 q N D hq hNq hD hDN).2.2.2
  rw [hs.2]
  unfold rawIdentificationBound
  linarith

end ThLean.BP.S5

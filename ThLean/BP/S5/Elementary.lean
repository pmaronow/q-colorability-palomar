module

public import ThLean.BP.S5.Support

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S5
open ThresholdFoundations

/-- P3-LOW-E01; pre-poisson: normalization, bounded means, and generating function. -/
def S5_E01Statement : Prop :=
  (∀ z : ℝ, 0 ≤ z →
    (∀ j, 0 ≤ poissonWeight z j ∧ poissonWeight z j ≤ 1) ∧
    HasSum (poissonWeight z) 1 ∧
    (∀ a : ℝ, 0 ≤ a → HasSum (fun j => poissonWeight z j * a^j) (Real.exp (z * (a - 1)))) ∧
    (∀ (B : ℝ) (b : ℕ → ℝ), 0 ≤ B → (∀ j, 0 ≤ b j ∧ b j ≤ B) →
      Summable (fun j => poissonWeight z j * b j) ∧
      0 ≤ poissonMixture z b ∧ poissonMixture z b ≤ B)) ∧
  (∀ j : ℕ, Continuous (fun z : ℝ => poissonWeight z j))

/-- P3-LOW-E02A; pre-split: choose the positions of one letter in a word. -/
def S5_E02AStatement : Prop :=
  ∀ (E : Type) [Fintype E] (c : E → ℕ) (e : E),
    wordFiberCard c = (∑ v, c v).choose (c e) *
      wordFiberCard (fun v : {v : E // v ≠ e} => c v.val)

/-- P3-LOW-E02; pre-split: multinomial fiber and uniform histogram probability. -/
def S5_E02Statement : Prop :=
  (∀ (E : Type) [Fintype E] (c : E → ℕ),
    wordFiberCard c * ∏ e, (c e).factorial = (∑ e, c e).factorial) ∧
  (∀ (E : Type) [Fintype E] [Nonempty E] (c : E → ℕ),
    uniformProb (fun x : Fin (∑ e, c e) → E =>
      ∀ e, (Finset.univ.filter (fun i => x i = e)).card = c e) =
    ((∑ e, c e).factorial : ℝ) /
      ((Fintype.card E : ℝ)^(∑ e, c e) * ∏ e, ((c e).factorial : ℝ)))

/-- P3-LOW-E03; pre-tails(b): weak factorial lower bound. -/
def S5_E03Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    0 < ((k : ℝ) / Real.exp 1)^k ∧
    ((k : ℝ) / Real.exp 1)^k ≤ (k.factorial : ℝ)

/-- P3-LOW-E04; pre-tails(b): factorial moment and integer upper tails. -/
def S5_E04Statement : Prop :=
  ∀ μ : ℝ, 0 ≤ μ →
    (∀ k : ℕ, HasSum (fun j => (j.choose k : ℝ) * poissonWeight μ j)
      (μ^k / (k.factorial : ℝ))) ∧
    (∀ k : ℕ, 1 ≤ k →
      (∑' j : ℕ, if k ≤ j then poissonWeight μ j else 0) ≤ μ^k / (k.factorial : ℝ) ∧
      μ^k / (k.factorial : ℝ) ≤ (Real.exp 1 * μ / k)^k ∧
      (∑' j : ℕ, if k < j then poissonWeight μ j else 0) ≤
        (Real.exp 1 * μ / k)^k)

/-- P3-LOW-E05; pre-tails(d): shifted tail without a mass ratio. -/
def S5_E05Statement : Prop :=
  ∀ (z : ℝ), 0 ≤ z → ∀ i : ℕ, 1 ≤ i →
    (∑' j : ℕ, if i ≤ j then poissonWeight z j else 0) ≤
      (Real.exp z - 1) * poissonWeight z (i - 1)

/-- P3-LOW-E06, scalar convolution part of pre-split. -/
def S5_E06AStatement : Prop :=
  ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ∀ m : ℕ,
    ∑ j ∈ Finset.range (m + 1), poissonWeight a j * poissonWeight b (m - j) =
      poissonWeight (a + b) m

/-- P3-LOW-E06, disjoint-block product mass; empty blocks have rate zero. -/
def S5_E06BStatement : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] (r : I → ℝ), (∀ i, 0 ≤ r i) →
  ∀ (p : I → J) (c : J → ℕ),
    HasSum (fun x : I → ℕ =>
      if ∀ j, ∑ i ∈ Finset.univ.filter (fun i => p i = j), x i = c j
      then ∏ i, poissonWeight (r i) (x i) else 0)
      (∏ j, poissonWeight (∑ i ∈ Finset.univ.filter (fun i => p i = j), r i) (c j))

/-- P3-LOW-E06; pre-split: independent Poisson sums and block independence. -/
def S5_E06Statement : Prop := S5_E06AStatement ∧ S5_E06BStatement

theorem S5_E06_assembly (ha : S5_E06AStatement) (hb : S5_E06BStatement) :
    S5_E06Statement := ⟨ha, hb⟩

/-- P3-LOW-E07; pre-poisson and low-large: integrable Poisson kernels and exponential tails. -/
def S5_E07Statement : Prop :=
  (∀ (m : ℕ) (p : ℝ), 0 < p →
    IntegrableOn (fun t : ℝ => poissonWeight (p * t) m) (Set.Ici 0) ∧
    (∫ t in Set.Ici 0, poissonWeight (p * t) m) = 1 / p) ∧
  (∀ c a : ℝ, 0 < c → 0 ≤ a →
    IntegrableOn (fun s : ℝ => Real.exp (-c * s)) (Set.Ici a) ∧
    (∫ s in Set.Ici a, Real.exp (-c * s)) = Real.exp (-c * a) / c)

/-- P3-LOW-E08; pre-poisson/low-integral: Tonelli with justified real conversion. -/
def S5_E08Statement : Prop :=
  (∀ (X I : Type) [MeasurableSpace X] [Countable I] (μ : Measure X)
      (f : I → X → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) →
    (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ) ∧
  (∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    AEMeasurable f μ → (∫⁻ x, f x ∂μ) ≠ ∞ →
    (∀ᵐ x ∂μ, f x ≠ ∞) ∧ Integrable (fun x => (f x).toReal) μ ∧
    (∫ x, (f x).toReal ∂μ) = (∫⁻ x, f x ∂μ).toReal) ∧
  (∀ (A I : Type) [Fintype A] [Nonempty A] [Fintype I] (f : I → A → ℝ),
    uniformMean (fun a => ∑ i, f i a) = ∑ i, uniformMean (f i))

/-- P3-LOW-E09; low-conditions/low-cor: logarithms lose to every positive power. -/
def S5_E09Statement : Prop :=
  (∀ a b : ℝ, 0 < a →
    Tendsto (fun n : ℕ => if n < 3 then 0 else (Real.log n)^b / (n : ℝ)^a)
      atTop (nhds 0)) ∧
  (∀ a : ℝ, 0 < a → Tendsto (fun n : ℕ => (n : ℝ)^(-a)) atTop (nhds 0)) ∧
  Tendsto (fun n : ℕ => Real.log n) atTop atTop ∧
  Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop

/-- P3-LOW-E10; low-conditions: iterated-logarithm ratio. -/
def S5_E10Statement : Prop :=
  ∀ A : ℝ, 0 < A →
    Tendsto (fun n : ℕ => if n < 16 then 0 else
      Real.log (A * Real.log (Real.log n)) / Real.log (Real.log n)) atTop (nhds 0)

end ThLean.BP.S5

module

public import ThLean.BP.S6.Credit

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S6

/-- Auxiliary saturation at failure; the frozen class itself is not changed. -/
def saturatedPotential {n : ℕ} (q : ℕ) (G : Graph n) (u : Fin n) : ℝ :=
  ThresholdFoundations.saturatedPotential q G u
def finiteStop {n M : ℕ} (q : ℕ) (x : Hist n M) : ℕ := finiteStoppedTime q x
def activeStart {n M : ℕ} (q : ℕ) (T : Hist n M → WithTop ℕ) (x : Hist n M) : Prop :=
  T x < (finiteStop q x : WithTop ℕ)
def degreeStart {n M : ℕ} (u : Fin n) (j : ℕ) (x : Hist n M) : WithTop ℕ :=
  firstFailure (fun m => j ≤ degree (tuplePrefix x m) u)
def suffixCredits {n M : ℕ} (q : ℕ) (u : Fin n) (s : WithTop ℕ) (x : Hist n M) : ℝ :=
  ∑ i : Fin M, if s ≤ (i.val : WithTop ℕ) ∧ Colorable q (tuplePrefix x i.val)
    then creditIncrement q (tuplePrefix x i.val) u (x i) else 0

def binomialMass (m : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  binomialWeight m p k
def binomialTail (m : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ThresholdFoundations.binomialTail m p (k : ℝ)

/-- P4-HIGH-26; every increment fits in the saturated budget, high-telescope. Paper label: `eq:high-telescope`; blueprint ID: `P4-HIGH-26`. -/
def S6_26Statement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u : Fin n) (e : Edge n),
    0 ≤ saturatedPotential q G u ∧ saturatedPotential q G u ≤ Real.log n ∧
    0 ≤ creditIncrement q G u e ∧
    creditIncrement q G u e ≤ saturatedPotential q (addPair G e) u - saturatedPotential q G u ∧
    creditIncrement q G u e ≤ Real.log n

/-- P4-HIGH-27; deterministic suffix telescope, eq. high-telescope. Paper label: `eq:high-telescope`; blueprint ID: `P4-HIGH-27`. -/
def S6_27Statement : Prop := ∀ (n q M : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (u : Fin n) (x : Hist n M) (s : WithTop ℕ),
    suffixCredits q u s x ≤ Real.log n * indicator (s < (finiteStop q x : WithTop ℕ))

/-- P4-HIGH-28; finite predictable averaging, thm. high-potential lines 337--351. Paper label: `thm:high-potential`; blueprint ID: `P4-HIGH-28`. -/
def S6_28Statement : Prop := ∀ (n q M : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (u : Fin n) (T : Hist n M → WithTop ℕ), IsFiniteStoppingTime T →
    uniformMean (stoppedOccupation q u T) ≤
      (2 / Real.log 2) * Real.log n * uniformProb (activeStart q T)

/-- P4-HIGH-30a; the occurrence-degree binomial law, cor. high-degree. Paper label: `cor:high-degree`; blueprint ID: `P4-HIGH-30a`. -/
def S6_30aStatement : Prop := ∀ (n m k : ℕ), 3 ≤ n → ∀ u : Fin n,
  uniformProb (fun x : Hist n m => degree (tupleGraph x) u = k) =
    binomialMass m (2 / (n : ℝ)) k

/-- P4-HIGH-30b; activation is a stopping time, cor. high-degree lines 386--391. Paper label: `cor:high-degree`; blueprint ID: `P4-HIGH-30b`. -/
def S6_30bStatement : Prop := ∀ (n q M j : ℕ), 3 ≤ n → 3 ≤ q → 1 ≤ j →
  ∀ u : Fin n,
    IsFiniteStoppingTime (degreeStart (M := M) u j) ∧
    (∀ (x : Hist n M) (m : ℕ),
      degreeStart u j x ≤ (m : WithTop ℕ) ↔ j ≤ degree (tuplePrefix x m) u) ∧
    (∀ x : Hist n M, activeStart q (degreeStart u j) x →
      1 ≤ M ∧ j ≤ degree (tuplePrefix x (M - 1)) u) ∧
    IsStoppingTime (degreeHittingTime u j) ∧
    (∀ (ω : EdgeStream (Fin n)) (m : ℕ),
      degreeHittingTime u j ω ≤ (m : WithTop ℕ) ↔ j ≤ degree (processGraph ω m) u)

/-- P4-HIGH-30; degree law and activation facts. Paper label: `cor:high-degree`; blueprint ID: `P4-HIGH-30`. -/
def S6_30Statement : Prop := S6_30aStatement ∧ S6_30bStatement

theorem S6_30_assembly (ha : S6_30aStatement) (hb : S6_30bStatement) :
    S6_30Statement := ⟨ha, hb⟩

/-- P4-HIGH-31a; occupation identity and activation-tail transport, cor. high-degree.
This separates finite-prefix bookkeeping from the stopping estimate. Paper label: `cor:high-degree`; blueprint ID: `P4-HIGH-31a`. -/
def S6_31aStatement : Prop := ∀ (n q M j : ℕ), 3 ≤ n → 3 ≤ q → 1 ≤ j →
  ∀ u : Fin n,
    (∑ m ∈ Finset.range M, rootGeMean n q m j u) =
      uniformMean (stoppedOccupation q u (degreeStart (M := M) u j)) ∧
    uniformProb (activeStart q (degreeStart (M := M) u j)) ≤
      binomialTail (M - 1) (2 / (n : ℝ)) j

/-- P4-HIGH-31b; binomial tail with the cap substituted, cor. high-degree. Paper label: `cor:high-degree`; blueprint ID: `P4-HIGH-31b`. -/
def S6_31bStatement : Prop := ∀ (n : ℕ) (Λ : ℝ) (j : ℕ),
  3 ≤ n → 0 < Λ → 1 ≤ j →
  binomialTail (cap Λ n - 1) (2 / (n : ℝ)) j ≤
    (2 * Real.exp 1 * Λ / j) ^ j

/-- P4-HIGH-31; root degree occupation bound, cor. high-degree. Paper label: `cor:high-degree`; blueprint ID: `P4-HIGH-31`. -/
def S6_31Statement : Prop := ∀ (n q : ℕ) (Λ : ℝ), 3 ≤ n → 3 ≤ q → 0 < Λ →
  ∀ (u : Fin n) (j : ℕ), 1 ≤ j →
    (∑ m ∈ Finset.range (cap Λ n), rootGeMean n q m j u) ≤
      (2 / Real.log 2) * Real.log n * (2 * Real.exp 1 * Λ / j) ^ j

theorem S6_31_assembly (h28 : S6_28Statement) (h30 : S6_30bStatement)
    (ha : S6_31aStatement) (hb : S6_31bStatement) : S6_31Statement := by
  intro n q Λ hn hq hΛ u j hj
  obtain ⟨heq, hprob⟩ := ha n q (cap Λ n) j hn hq hj u
  rw [heq]
  have hstop := (h30 n q (cap Λ n) j hn hq hj u).1
  have hp := hprob.trans (hb n Λ j hn hΛ hj)
  have hc : 0 ≤ (2 / Real.log 2) * Real.log (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    exact mul_nonneg (div_nonneg (by norm_num) (le_of_lt (Real.log_pos (by norm_num))))
      (Real.log_nonneg hn1)
  exact (h28 n q (cap Λ n) hn hq u _ hstop).trans (mul_le_mul_of_nonneg_left hp hc)

end ThLean.BP.S6

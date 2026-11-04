module

public import ThLean.BP.SA.Basics
public import ThLean.BP.SA.Quantiles
public import ThLean.BP.SA.Tree
public import ThLean.BP.SA.Transfer

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.SA
open ThresholdFoundations

/-- P5-C60, bounded normalized quantiles on the valid tail, A:374--378. Paper label: `thm:red-convergence`; blueprint: `P5-C60`. -/
def SA_C60aStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ η : ℝ, gamma q + 1 < Λ → 0 < η → η ≤ 1 / 2 →
    ∀ n : ℕ, 2 * q ≤ n → 0 ≤ xi q Λ η n ∧ xi q Λ η n ≤ Λ

/-- P5-C60; convergence at one fixed quantile level, A:374--378. Paper label: `thm:red-convergence`; blueprint: `P5-C60`. -/
def SA_C60Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (Λ η K : ℝ) (δ : ℕ → ℝ) (n₁ : ℕ),
    gamma q + 1 < Λ → AdmissibleError δ → 0 < η → η ≤ etaZero Λ →
    WindowAt q Λ δ η K n₁ →
    ∃ α : ℝ, α ∈ Set.Icc 0 Λ ∧ Tendsto (xi q Λ η) atTop (𝓝 α)

/-- P5-C61, the exact interval from the preliminary centre bounds. Paper label: `thm:red-convergence`; blueprint: `P5-C61`. -/
def SA_C61aStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ η α : ℝ, gamma q + 1 < Λ → 0 < η → η ≤ 1 / 2 →
    Tendsto (xi q Λ η) atTop (𝓝 α) → α ∈ Set.Icc (1 / 2 : ℝ) (gamma q)

/-- P5-C61, upper-quantile convergence from the vanishing window. Paper label: `thm:red-convergence`; blueprint: `P5-C61`. -/
def SA_C61bStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (Λ η K α : ℝ) (δ : ℕ → ℝ) (n₁ : ℕ),
    gamma q + 1 < Λ → AdmissibleError δ → 0 < η → η ≤ etaZero Λ →
    WindowAt q Λ δ η K n₁ → Tendsto (xi q Λ η) atTop (𝓝 α) →
    Tendsto (fun n : ℕ => (upperLocation q Λ η n : ℝ) / n) atTop (𝓝 α)

/-- P5-C61; both quantiles and the exact interval. Paper label: `thm:red-convergence`; blueprint: `P5-C61`. -/
def SA_C61Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (Λ η K α : ℝ) (δ : ℕ → ℝ) (n₁ : ℕ),
    gamma q + 1 < Λ → AdmissibleError δ → 0 < η → η ≤ etaZero Λ →
    WindowAt q Λ δ η K n₁ → Tendsto (xi q Λ η) atTop (𝓝 α) →
    α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) ∧
    Tendsto (fun n : ℕ => (upperLocation q Λ η n : ℝ) / n) atTop (𝓝 α)

/-- P5-C62, identify fixed-level limits by the quantile sandwich, A:380--388. Paper label: `thm:red-convergence`; blueprint: `P5-C62`. -/
def SA_C62aStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q + 1 < Λ →
    (∀ η : ℝ, 0 < η → η ≤ etaZero Λ →
      ∃ α : ℝ, α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) ∧
        Tendsto (xi q Λ η) atTop (𝓝 α) ∧
        Tendsto (fun n : ℕ => (upperLocation q Λ η n : ℝ) / n) atTop (𝓝 α)) →
    ∃ α : ℝ, α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) ∧ QuantileLimits q Λ α

/-- P5-C62; one common limit for every small level, A:380--388. Paper label: `thm:red-convergence`; blueprint: `P5-C62`. -/
def SA_C62Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (Λ : ℝ) (δ : ℕ → ℝ), gamma q + 1 < Λ →
    AdmissibleError δ → WindowFamily q Λ δ →
    ∃ α : ℝ, α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) ∧ QuantileLimits q Λ α

theorem SA_C62_assembly (h60 : SA_C60Statement) (h61 : SA_C61Statement)
    (hid : SA_C62aStatement) : SA_C62Statement := by
  intro q hq Λ δ hΛ hδ hw
  apply hid q hq Λ hΛ
  intro η hη hη₀
  obtain ⟨K, n₁, hwin⟩ := hw η hη hη₀
  obtain ⟨α, _, hα⟩ := h60 q hq Λ η K δ n₁ hΛ hδ hη hη₀ hwin
  obtain ⟨hb, hu⟩ := h61 q hq Λ η K α δ n₁ hΛ hδ hη hη₀ hwin hα
  exact ⟨α, hb, hα, hu⟩

/-- P5-C63, lower process zero-one law; A:390--392. Paper label: `thm:red-convergence`; blueprint: `P5-C63`. -/
def SA_C63aStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ α : ℝ, gamma q + 1 < Λ →
    α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) → QuantileLimits q Λ α →
    ∀ c : ℝ, 0 ≤ c → c < α →
      Tendsto (fun n : ℕ => processSurvival (V := Fin n) q (Nat.floor (c * n))) atTop (𝓝 1)

/-- P5-C63, upper process law, also above the cap; A:390--392. Paper label: `thm:red-convergence`; blueprint: `P5-C63`. -/
def SA_C63bStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ α : ℝ, gamma q + 1 < Λ →
    α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) → QuantileLimits q Λ α →
    ∀ c : ℝ, α < c →
      Tendsto (fun n : ℕ => processSurvival (V := Fin n) q (Nat.floor (c * n))) atTop (𝓝 0)

/-- P5-C63; complete edge-process zero-one law. Paper label: `thm:red-convergence`; blueprint: `P5-C63`. -/
def SA_C63Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ α : ℝ, gamma q + 1 < Λ →
    α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) → QuantileLimits q Λ α → ProcessLimits q α

theorem SA_C63_assembly (ha : SA_C63aStatement) (hb : SA_C63bStatement) :
    SA_C63Statement := by
  intro q hq Λ α hΛ hα hlim
  exact ⟨ha q hq Λ α hΛ hα hlim, hb q hq Λ α hΛ hα hlim⟩

/-- P5-C64, lower uniform-model law, A:394--398. Paper label: `thm:red-convergence`; blueprint: `P5-C64`. -/
def SA_C64aStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ α : ℝ, gamma q + 1 < Λ →
    α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) → ProcessLimits q α →
    ∀ c : ℝ, 0 ≤ c → c < α →
      Tendsto (fun n : ℕ => simpleProbability (V := Fin n) q (Nat.floor (c * n))) atTop (𝓝 1)

/-- P5-C64, upper uniform-model law and eventual validity, A:394--398. Paper label: `thm:red-convergence`; blueprint: `P5-C64`. -/
def SA_C64bStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ α : ℝ, gamma q + 1 < Λ →
    α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) → ProcessLimits q α →
    (∀ c : ℝ, α < c →
      Tendsto (fun n : ℕ => simpleProbability (V := Fin n) q (Nat.floor (c * n))) atTop (𝓝 0)) ∧
    (∀ c : ℝ, 0 ≤ c → ∀ᶠ n : ℕ in atTop, Nat.floor (c * n) ≤ n.choose 2)

/-- P5-C64; complete uniform-model zero-one law. Paper label: `thm:red-convergence`; blueprint: `P5-C64`. -/
def SA_C64Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ α : ℝ, gamma q + 1 < Λ →
    α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) → ProcessLimits q α → SimpleLimits q α ∧
    (∀ c : ℝ, 0 ≤ c → ∀ᶠ n : ℕ in atTop, Nat.floor (c * n) ≤ n.choose 2)

theorem SA_C64_assembly (ha : SA_C64aStatement) (hb : SA_C64bStatement) :
    SA_C64Statement := by
  intro q hq Λ α hΛ hα hlim
  obtain ⟨hu, hv⟩ := hb q hq Λ α hΛ hα hlim
  exact ⟨⟨ha q hq Λ α hΛ hα hlim, hu⟩, hv⟩

/-- P5-C65, lower sparse-binomial law; A:400--410. Paper label: `thm:red-convergence`; blueprint: `P5-C65`. -/
def SA_C65aStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ α : ℝ, 1 / 2 ≤ α → SimpleLimits q α →
    ∀ d : ℝ, 0 ≤ d → d < 2 * α →
      Tendsto (fun n : ℕ => sparseProbability q n d) atTop (𝓝 1)

/-- P5-C65, upper sparse-binomial law; A:400--410. Paper label: `thm:red-convergence`; blueprint: `P5-C65`. -/
def SA_C65bStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ α : ℝ, 1 / 2 ≤ α → SimpleLimits q α →
    ∀ d : ℝ, 2 * α < d →
      Tendsto (fun n : ℕ => sparseProbability q n d) atTop (𝓝 0)

/-- P5-C65; complete binomial-model zero-one law. Paper label: `thm:red-convergence`; blueprint: `P5-C65`. -/
def SA_C65Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ α : ℝ, 1 / 2 ≤ α → SimpleLimits q α → BinomialLimits q α

theorem SA_C65_assembly (ha : SA_C65aStatement) (hb : SA_C65bStatement) :
    SA_C65Statement := by
  intro q hq α hα hlim
  exact ⟨ha q hq α hα hlim, hb q hq α hα hlim⟩

/-- Full output, preserving quantile and all three graph-model conclusions. -/
def ConvergenceResult (q : ℕ) (Λ α : ℝ) : Prop :=
  α ∈ Set.Icc (1 / 2 : ℝ) (gamma q) ∧
  QuantileLimits q Λ α ∧ ProcessLimits q α ∧ SimpleLimits q α ∧ BinomialLimits q α

/-- P5-C66; thm:red-convergence, R:15--26 and A:370--412. Paper label: `thm:red-convergence`; blueprint: `P5-C66`. -/
def SA_C66Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (Λ : ℝ) (δ : ℕ → ℝ), gamma q + 1 < Λ →
    AdmissibleError δ → WindowFamily q Λ δ → ∃ α : ℝ, ConvergenceResult q Λ α

theorem SA_C66_assembly (h62 : SA_C62Statement) (h63 : SA_C63Statement)
    (h64 : SA_C64Statement) (h65 : SA_C65Statement) : SA_C66Statement := by
  intro q hq Λ δ hΛ hδ hw
  obtain ⟨α, hα, hquant⟩ := h62 q hq Λ δ hΛ hδ hw
  have hp := h63 q hq Λ α hΛ hα hquant
  have hs := (h64 q hq Λ α hΛ hα hp).1
  exact ⟨α, hα, hquant, hp, hs, h65 q hq α hα.1 hs⟩

/-- P5-C67; uniqueness independent of cap and error sequence, A:414. Paper label: `thm:red-convergence`; blueprint: `P5-C67`. -/
def SA_C67Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
    ProcessLimits q α → ProcessLimits q β → α = β

/-- P5-C69; thm:intro-main, retaining quantile and process conclusions. Paper label: `thm:intro-main`; blueprint: `P5-C69`. -/
def SA_C69Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ α : ℝ, ConvergenceResult q (capDensity q) α

/-- P5-C60 assembly: the comparison tree supplies the one-level limit. -/
theorem SA_C60_assembly (h01 : SA_F01Statement) (hbounds : SA_C60aStatement)
    (h28 : SA_Q28Statement) (h39 : SA_T39Statement) (htree : SA_T38Statement) :
    SA_C60Statement := by
  intro q hq Λ η K δ n₁ hΛ hδ hη hη₀ hw
  have hp := (h01 q hq).2.2 Λ hΛ
  have hhalf : η ≤ 1 / 2 := le_trans hη₀ (le_of_lt (lt_trans hp.2.2.1 hp.2.2.2))
  obtain ⟨s₀, hqs, hcmp⟩ := h28 q hq Λ η K δ n₁ hΛ hδ hη hη₀ hw
  have hg := (h39 Λ K δ hp.1 hw.1 hδ).1
  have hbound : ∀ n : ℕ, s₀ ≤ n → |xi q Λ η n| ≤ Λ := by
    intro n hn
    have h := hbounds q hq Λ η hΛ hη hhalf n (hqs.trans hn)
    rw [abs_of_nonneg h.1]
    exact h.2
  obtain ⟨α, hα⟩ := htree (Real.exp 2) (comparisonError δ Λ K) hg
    (xi q Λ η) s₀ Λ hp.1.le hbound hcmp
  refine ⟨α, ⟨?_, ?_⟩, hα⟩
  · apply ge_of_tendsto hα
    filter_upwards [eventually_ge_atTop (2 * q)] with n hn
    exact (hbounds q hq Λ η hΛ hη hhalf n hn).1
  · apply le_of_tendsto hα
    filter_upwards [eventually_ge_atTop (2 * q)] with n hn
    exact (hbounds q hq Λ η hΛ hη hhalf n hn).2

/-- P5-C61 assembly: centre bounds and the vanishing window. -/
theorem SA_C61_assembly (h01 : SA_F01Statement) (ha : SA_C61aStatement)
    (hb : SA_C61bStatement) : SA_C61Statement := by
  intro q hq Λ η K α δ n₁ hΛ hδ hη hη₀ hw hα
  have hp := (h01 q hq).2.2 Λ hΛ
  have hhalf : η ≤ 1 / 2 := le_trans hη₀ (le_of_lt (lt_trans hp.2.2.1 hp.2.2.2))
  exact ⟨ha q hq Λ η α hΛ hη hhalf hα,
    hb q hq Λ η K α δ n₁ hΛ hδ hη hη₀ hw hα⟩

/-- P5-C69 assembly; the only external input is Section 7's actual window contract. -/
theorem SA_C69_assembly (h01 : SA_F01Statement) (h68 : EpsilonAdmissibleStatement)
    (h66 : SA_C66Statement) (hw : ProofWindowStatement) : SA_C69Statement := by
  intro q hq
  have hγ := (h01 q hq).2.1
  have hΛ : gamma q + 1 < capDensity q := by unfold capDensity; linarith
  have hΛpos : 0 < capDensity q := by unfold capDensity; linarith
  apply h66 q hq (capDensity q) epsilon hΛ h68.1
  intro η hη hη₀
  obtain ⟨N, hN, hbound⟩ := hw q hq η hη hη₀
  refine ⟨6 * capDensity q / η ^ 2, N, ?_, ?_⟩
  · positivity
  · intro n hn
    exact hbound n (le_trans (le_max_right _ _) hn)
end ThLean.BP.SA

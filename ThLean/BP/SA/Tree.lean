module

public import ThLean.BP.SA.Common

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.SA
open ThresholdFoundations

/-- P5-T30; adjacent block sizes, A:265. Natural division is intentional here. Paper label: `lem:conv-tree`; blueprint: `P5-T30`. -/
def SA_T30Statement : Prop :=
  ∀ ℓ n : ℕ, 2 ≤ ℓ → ℓ ^ 2 ≤ n →
    n = (n / ℓ) * ℓ + n % ℓ ∧ ℓ ≤ n / ℓ ∧ n % ℓ < ℓ ∧
    ∃ b : List ℕ, b.length = n / ℓ ∧ b.sum = n ∧
      b.count (ℓ + 1) = n % ℓ ∧ b.count ℓ = n / ℓ - n % ℓ ∧
      ∀ x ∈ b, x = ℓ ∨ x = ℓ + 1

/-- P5-T31; ordered balanced tree construction, A:267. Paper label: `lem:conv-tree`; blueprint: `P5-T31`. -/
def SA_T31Statement : Prop :=
  ∀ b : List ℕ, b ≠ [] → (∀ x ∈ b, 0 < x) →
    ∃ t : BlockTree, leafList t = b ∧ Halves t ∧ t.size = b.sum ∧
      ∀ ℓ : ℕ, (∀ x ∈ b, x = ℓ ∨ x = ℓ + 1) → t.Balanced ℓ

/-- P5-T32, size bounds; A:276--286. Paper label: `lem:conv-tree`; blueprint: `P5-T32`. -/
def SA_T32aStatement : Prop :=
  ∀ (ℓ : ℕ) (t : BlockTree), 2 ≤ ℓ → t.Balanced ℓ →
    t.leaves * ℓ ≤ t.size ∧ t.size ≤ t.leaves * (ℓ + 1)

/-- P5-T32, quarter-to-three-quarter child ratios; eq:conv-children. Paper label: `lem:conv-tree`; blueprint: `P5-T32`. -/
def SA_T32bStatement : Prop :=
  ∀ (ℓ : ℕ) (a b : BlockTree), 2 ≤ ℓ → (BlockTree.node a b).Balanced ℓ →
    ((a.size + b.size : ℕ) : ℝ) / 4 ≤ a.size ∧
    (a.size : ℝ) ≤ 3 * ((a.size + b.size : ℕ) : ℝ) / 4 ∧
    ((a.size + b.size : ℕ) : ℝ) / 4 ≤ b.size ∧
    (b.size : ℝ) ≤ 3 * ((a.size + b.size : ℕ) : ℝ) / 4

/-- P5-T32, height growth along a longest branch; eq:conv-growth. Paper label: `lem:conv-tree`; blueprint: `P5-T32`. -/
def SA_T32cStatement : Prop :=
  ∀ (ℓ : ℕ) (t : BlockTree), 2 ≤ ℓ → t.Balanced ℓ →
    (ℓ : ℝ) * (4 / 3 : ℝ) ^ t.height ≤ t.size

/-- P5-T32; all tree geometry estimates. Paper label: `lem:conv-tree`; blueprint: `P5-T32`. -/
def SA_T32Statement : Prop := SA_T32aStatement ∧ SA_T32bStatement ∧ SA_T32cStatement

theorem SA_T32_assembly (ha : SA_T32aStatement) (hb : SA_T32bStatement)
    (hc : SA_T32cStatement) : SA_T32Statement := ⟨ha, hb, hc⟩

/-- P5-T33, finite tree induction; eq:conv-induction. Paper label: `lem:conv-tree`; blueprint: `P5-T33`. -/
def SA_T33aStatement : Prop :=
  ∀ (u₀ : ℝ) (g : ℝ → ℝ), 1 ≤ u₀ →
    (∀ u : ℝ, 1 ≤ u → 0 ≤ g u) → AntitoneOn g (Set.Ici u₀) →
    ∀ (ξ : ℕ → ℝ) (s₀ ℓ : ℕ), Compares ξ g s₀ → max s₀ 2 ≤ ℓ →
      4 * u₀ ≤ (ℓ : ℝ) → ∀ t : BlockTree, t.Balanced ℓ →
        ξ ℓ - g ℓ -
          (∑ i ∈ Finset.range t.height, g ((ℓ : ℝ) / 4 * (4 / 3 : ℝ) ^ (i + 1))) ≤ ξ t.size

/-- P5-T34; bounded multiplicity of logarithmic buckets, A:239--263. Paper label: `lem:conv-tree`; blueprint: `P5-T34`. -/
def SA_T34Statement : Prop :=
  ∀ h : ℝ, 0 < h → ∀ m j : ℕ,
    ((Finset.Icc 1 m).filter (fun i => Nat.floor ((i : ℝ) * h) = j)).card ≤
      Nat.ceil (1 / h) + 1

/-- P5-T35; finite condensation inequality before any use of a path tsum. Paper label: `lem:conv-tree`; blueprint: `P5-T35`. -/
def SA_T35Statement : Prop :=
  ∀ (u₀ : ℝ) (g : ℝ → ℝ), AnalyticError u₀ g → ∀ K : ℕ,
    u₀ ≤ Real.exp K → ∀ ℓ : ℝ, 4 * Real.exp K ≤ ℓ → ∀ m : ℕ,
      (∑ i ∈ Finset.range m, g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1))) ≤
        ((Nat.ceil (1 / Real.log (4 / 3 : ℝ)) + 1 : ℕ) : ℝ) *
          ∑' k : ℕ, g (Real.exp ((K + k : ℕ) : ℝ))

/-- P5-T36; summability, tail bound, and vanishing path error; A:244--263. Paper label: `lem:conv-tree`; blueprint: `P5-T36`. -/
def SA_T36Statement : Prop :=
  ∀ (u₀ : ℝ) (g : ℝ → ℝ), AnalyticError u₀ g →
    (∀ ℓ : ℝ, 4 * u₀ ≤ ℓ →
      Summable (fun i : ℕ => g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1))) ∧ 0 ≤ pathError g ℓ) ∧
    (∀ K : ℕ, u₀ ≤ Real.exp K → ∀ ℓ : ℝ, 4 * Real.exp K ≤ ℓ →
      pathError g ℓ ≤ ((Nat.ceil (1 / Real.log (4 / 3 : ℝ)) + 1 : ℕ) : ℝ) *
        ∑' k : ℕ, g (Real.exp ((K + k : ℕ) : ℝ))) ∧
    Tendsto g atTop (𝓝 0) ∧ Tendsto (pathError g) atTop (𝓝 0)

/-- P5-T33, from balanced finite trees to a uniform tail loss; A:308--312. Paper label: `lem:conv-tree`; blueprint: `P5-T33`. -/
def SA_T33bStatement : Prop :=
  ∀ (u₀ : ℝ) (g : ℝ → ℝ), AnalyticError u₀ g →
    ∀ (ξ : ℕ → ℝ) (s₀ : ℕ), Compares ξ g s₀ →
      ∃ s₁ : ℕ, 1 ≤ s₁ ∧ ∀ ℓ : ℕ, s₁ ≤ ℓ →
        0 ≤ g ℓ + pathError g ℓ ∧
        ∀ n : ℕ, ℓ ^ 2 ≤ n → ξ ℓ - (g ℓ + pathError g ℓ) ≤ ξ n

/-- P5-T33; finite estimate and its uniform tail consequence. Paper label: `lem:conv-tree`; blueprint: `P5-T33`. -/
def SA_T33Statement : Prop := SA_T33aStatement ∧ SA_T33bStatement

theorem SA_T33_assembly (ha : SA_T33aStatement) (hb : SA_T33bStatement) :
    SA_T33Statement := ⟨ha, hb⟩

/-- P5-T37; bounded sequences with vanishing one-sided tail loss, A:308--312. Paper label: `lem:conv-tree`; blueprint: `P5-T37`. -/
def SA_T37Statement : Prop :=
  ∀ (ξ E : ℕ → ℝ) (s₀ s₁ : ℕ) (B : ℝ), 1 ≤ s₀ → 1 ≤ s₁ → 0 ≤ B →
    (∀ n : ℕ, s₀ ≤ n → |ξ n| ≤ B) →
    (∀ ℓ : ℕ, s₁ ≤ ℓ → 0 ≤ E ℓ) → Tendsto E atTop (𝓝 0) →
    (∀ ℓ : ℕ, s₁ ≤ ℓ → ∀ n : ℕ, ℓ ^ 2 ≤ n → ξ ℓ - E ℓ ≤ ξ n) →
      Tendsto ξ atTop (𝓝 (Filter.limsup ξ atTop))

/-- P5-T38; lem:conv-tree, allowing nonnegative error functions. Paper label: `lem:conv-tree`; blueprint: `P5-T38`. -/
def SA_T38Statement : Prop :=
  ∀ (u₀ : ℝ) (g : ℝ → ℝ), AnalyticError u₀ g →
    ∀ (ξ : ℕ → ℝ) (s₀ : ℕ) (B : ℝ), 0 ≤ B →
      (∀ n : ℕ, s₀ ≤ n → |ξ n| ≤ B) → Compares ξ g s₀ →
      ∃ α : ℝ, Tendsto ξ atTop (𝓝 α)

/-- P5-T39; the paper's error function satisfies the tree hypotheses, A:374--378. Paper label: `lem:conv-tree`; blueprint: `P5-T39`. -/
def SA_T39Statement : Prop :=
  ∀ (Λ K : ℝ) (δ : ℕ → ℝ), 0 < Λ → 0 < K → AdmissibleError δ →
    AnalyticError (Real.exp 2) (comparisonError δ Λ K) ∧
    (∀ u : ℝ, 1 ≤ u → 0 < comparisonError δ Λ K u) ∧
    Tendsto δ atTop (𝓝 0)

/-- P5-E04; polynomial-geometric summability and vanishing tails. Paper label: `lem:conv-tree`; blueprint: `P5-E04`. -/
def SA_E04Statement : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ d : ℕ,
    Summable (fun k : ℕ => (k : ℝ) ^ d * r ^ k) ∧
    Tendsto (fun N : ℕ => ∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ d * r ^ (N + k)) atTop (𝓝 0)

/-- P5-E05; the positive-index p-series, T:48--52. Paper label: `thm:proof-window`; blueprint: `P5-E05`. -/
def SA_E05Statement : Prop :=
  ∀ p : ℝ, 1 < p → Summable (fun n : ℕ => Real.rpow (n + 1 : ℝ) (-p))


/-- P5-T38 assembly from a vanishing tail loss and the limsup criterion. -/
theorem SA_T38_assembly (htail : SA_T33bStatement) (herr : SA_T36Statement)
    (hlim : SA_T37Statement) : SA_T38Statement := by
  intro u₀ g hg ξ s₀ B hB hξ hcmp
  obtain ⟨s₁, hs₁, ht⟩ := htail u₀ g hg ξ s₀ hcmp
  have he := herr u₀ g hg
  have hzero : Tendsto (fun n : ℕ => g n + pathError g n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_add] using
      (he.2.2.1.add he.2.2.2).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine ⟨Filter.limsup ξ atTop, ?_⟩
  exact hlim ξ (fun n => g n + pathError g n) s₀ s₁ B hcmp.1 hs₁ hB hξ
    (fun ℓ hℓ => (ht ℓ hℓ).1) hzero (fun ℓ hℓ => (ht ℓ hℓ).2)
end ThLean.BP.SA

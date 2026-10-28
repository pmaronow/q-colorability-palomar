import ThLean.BP.SA.Common

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.SA
open ThresholdFoundations

/-- P5-I10; def:pre-multigraph and Appendix A:19,72. Paper label: `lem:conv-interp`; blueprint: `P5-I10`. -/
def SA_I10Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 1 ≤ q →
    (∀ G G' : MGraph V, edgeSupport G = edgeSupport G' → colorings q G = colorings q G') ∧
    (∀ (G : MGraph V) (v : V), 0 < G s(v, v) → ¬ Colorable q G) ∧
    (∀ (G : MGraph V) (x y : V) (σ : V → Fin q),
      IsColoring q (addEdge G s(x, y)) σ ↔ IsColoring q G σ ∧ σ x ≠ σ y)

/-- P5-I11, signed algebraic joint-count leaf; lem:pre-split(a), A:57--70. Paper label: `lem:conv-interp`; blueprint: `P5-I11`. -/
def SA_I11aStatement : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D] [Nonempty D]
    (ν : D → ℝ) (μ : ℝ),
    (∀ e, 0 ≤ ν e) → (∑ e, ν e) = 1 →
    ∀ z : D → ℕ,
      weightedListMean μ ν (fun xs => indicator (∀ e, xs.count e = z e)) =
        ∏ e, poissonWeight (μ * ν e) (z e)

/-- P5-I11, signed algebraic support reduction; A:57--70. Paper label: `lem:conv-interp`; blueprint: `P5-I11`. -/
def SA_I11bStatement : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D] (rate : D → ℝ) (F : Finset D → ℝ),
    Summable (fun z : D → ℕ =>
      (∏ e, poissonWeight (rate e) (z e)) * F (Finset.univ.filter (fun e => 0 < z e))) ∧
    (∑' z : D → ℕ, (∏ e, poissonWeight (rate e) (z e)) *
      F (Finset.univ.filter (fun e => 0 < z e))) = supportMean F rate

/-- P5-I11, probability and positivity of support weights; A:57--70. Paper label: `lem:conv-interp`; blueprint: `P5-I11`. -/
def SA_I11cStatement : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D] (rate : D → ℝ),
    (∀ e, 0 ≤ rate e) →
    (∀ T : Finset D, 0 ≤ supportWeight rate T) ∧
    (∑ T ∈ Finset.univ.powerset, supportWeight rate T) = 1 ∧
    (∀ F : Finset D → ℝ, (∀ T, 0 ≤ F T) → 0 ≤ supportMean F rate)

/-- P5-I11; all parts of finite Poisson marking and its support law. Paper label: `lem:conv-interp`; blueprint: `P5-I11`. -/
def SA_I11Statement : Prop := SA_I11aStatement ∧ SA_I11bStatement ∧ SA_I11cStatement

theorem SA_I11_assembly (ha : SA_I11aStatement) (hb : SA_I11bStatement)
    (hc : SA_I11cStatement) : SA_I11Statement := ⟨ha, hb, hc⟩

/-- P5-I12a; finite coordinate derivative replacing infinite differentiation in A:57--70. Paper label: `lem:conv-interp`; blueprint: `P5-I12a`. -/
def SA_I12aStatement : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D]
    (F : Finset D → ℝ) (rate : D → ℝ) (e : D),
    HasDerivAt (fun t : ℝ => supportMean F (Function.update rate e t))
      (supportMean (fun T => F (insert e T) - F T) rate) (rate e)

/-- P5-I12a, bounded expected increment at nonnegative rates; A:57--70. Paper label: `lem:conv-interp`; blueprint: `P5-I12a`. -/
def SA_I12cStatement : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D]
    (F : Finset D → ℝ) (rate : D → ℝ) (e : D) (B : ℝ),
    (∀ x, 0 ≤ rate x) → 0 ≤ B → (∀ T, |F T| ≤ B) →
    |supportMean (fun T => F (insert e T) - F T) rate| ≤ 2 * B

/-- P5-I12b; affine-rate chain rule, A:61,81--85. Paper label: `lem:conv-interp`; blueprint: `P5-I12b`. -/
def SA_I12bStatement : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D]
    (F : Finset D → ℝ) (α β : D → ℝ),
    ContDiff ℝ 1 (fun t : ℝ => supportMean F (fun e => α e * t + β e)) ∧
    ∀ t : ℝ, HasDerivAt (fun t : ℝ => supportMean F (fun e => α e * t + β e))
      (∑ e, α e * supportMean (fun T => F (insert e T) - F T)
        (fun e => α e * t + β e)) t

/-- P5-I13, absolutely convergent analytic bridge from frozen chiBar; A:41--70. Paper label: `lem:conv-interp`; blueprint: `P5-I13`. -/
def SA_I13aStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ μ : Fin 3 → ℝ,
    Summable (fun k : Fin 3 → ℕ =>
      (∏ i : Fin 3, poissonWeight (μ i) (k i)) * interpolationCoefficient q n₁ n₂ k) ∧
    chiBar q n₁ n₂ μ = finiteChiBar q n₁ n₂ μ

/-- P5-I13, endpoint laws and the one-vertex case; A:21--59, eq:conv-rho1. Paper label: `lem:conv-interp`; blueprint: `P5-I13`. -/
def SA_I13bStatement : Prop :=
  (∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ c : ℝ, 0 ≤ c →
    finiteChi q n₁ n₂ c 0 = rho q n₁ c * rho q n₂ c ∧
    finiteChi q n₁ n₂ c c = rho q (n₁ + n₂) c) ∧
  (∀ q n : ℕ, 1 ≤ q → 1 ≤ n → rho q n 0 = 1) ∧
  (∀ q : ℕ, 1 ≤ q → ∀ c : ℝ, 0 ≤ c → rho q 1 c = Real.exp (-c))

/-- P5-I13; complete interpolation-law identification. Paper label: `lem:conv-interp`; blueprint: `P5-I13`. -/
def SA_I13Statement : Prop := SA_I13aStatement ∧ SA_I13bStatement

theorem SA_I13_assembly (ha : SA_I13aStatement) (hb : SA_I13bStatement) :
    SA_I13Statement := ⟨ha, hb⟩

/-- P5-I14, equivalence relation and add-one criterion including loops; A:72--79. Paper label: `lem:conv-interp`; blueprint: `P5-I14`. -/
def SA_I14aStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ) (G : MGraph V), 1 ≤ q → Colorable q G →
    Equivalence (Frozen q G) ∧ Loopless G ∧
    ∀ x y : V, (¬ Colorable q (addEdge G s(x, y))) ↔ Frozen q G x y

/-- P5-I14, ordered-pair counting in whole-graph frozen classes; A:72--79. Paper label: `lem:conv-interp`; blueprint: `P5-I14`. -/
def SA_I14bStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ) (G : MGraph V) (T : Finset V), 1 ≤ q →
    (∑ x ∈ T, ∑ y ∈ T,
      (indicator (Colorable q G) - indicator (Colorable q (addEdge G s(x, y))))) =
    if Colorable q G then
      ∑ C ∈ frozenClasses q G, ((C ∩ T).card : ℝ) ^ 2 else 0

/-- P5-I14; add-one loss and the frozen partition. Paper label: `lem:conv-interp`; blueprint: `P5-I14`. -/
def SA_I14Statement : Prop := SA_I14aStatement ∧ SA_I14bStatement

theorem SA_I14_assembly (ha : SA_I14aStatement) (hb : SA_I14bStatement) :
    SA_I14Statement := ⟨ha, hb⟩

/-- P5-I15; eq:conv-square, with real division and positive denominators. Paper label: `lem:conv-interp`; blueprint: `P5-I15`. -/
def SA_I15Statement : Prop :=
  ∀ a b r s : ℝ, 0 < r → 0 < s →
    a ^ 2 / r + b ^ 2 / s - (a + b) ^ 2 / (r + s) =
      (s * a - r * b) ^ 2 / (r * s * (r + s)) ∧
    0 ≤ a ^ 2 / r + b ^ 2 / s - (a + b) ^ 2 / (r + s)

/-- P5-I16, partial derivatives of the finite extension; A:63--79. Paper label: `lem:conv-interp`; blueprint: `P5-I16`. -/
def SA_I16aStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ →
    ∀ (μ : Fin 3 → ℝ), (∀ j, 0 ≤ μ j) → ∀ j : Fin 3,
      HasDerivAt (fun t => finiteChiBar q n₁ n₂ (Function.update μ j t))
        (-supportMean (fun T => addLoss q n₁ n₂ j (supportGraph T)) (markRate n₁ n₂ μ)) (μ j)

/-- P5-I16, derivative along interpolation; eq:conv-derivative. Paper label: `lem:conv-interp`; blueprint: `P5-I16`. -/
def SA_I16bStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ c : ℝ, 0 < c →
    ∀ θ : ℝ, θ ∈ Set.Icc 0 c →
      HasDerivAt (finiteChi q n₁ n₂ c) (driftMean q n₁ n₂ c θ) θ

/-- P5-I16, pointwise and expected drift signs; eq:conv-square. Paper label: `lem:conv-interp`; blueprint: `P5-I16`. -/
def SA_I16cStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ →
    (∀ G : MGraph (Fin (n₁ + n₂)), 0 ≤ drift q n₁ n₂ G) ∧
    ∀ c : ℝ, 0 ≤ c → ∀ θ : ℝ, θ ∈ Set.Icc 0 c → 0 ≤ driftMean q n₁ n₂ c θ

/-- P5-I16; all requested derivative and sign conclusions. Paper label: `lem:conv-interp`; blueprint: `P5-I16`. -/
def SA_I16Statement : Prop := SA_I16aStatement ∧ SA_I16bStatement ∧ SA_I16cStatement

theorem SA_I16_assembly (ha : SA_I16aStatement) (hb : SA_I16bStatement)
    (hc : SA_I16cStatement) : SA_I16Statement := ⟨ha, hb, hc⟩

/-- P5-I17; lem:conv-interp, eq:conv-product. Paper label: `lem:conv-interp`; blueprint: `P5-I17`. -/
def SA_I17Statement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ c : ℝ, 0 ≤ c →
    rho q n₁ c * rho q n₂ c ≤ rho q (n₁ + n₂) c


/-- Finite-support smoothness needed for the frozen interpolation bridge. Paper label: `lem:conv-interp`; blueprint: `P5-I12b`. -/
def SA_I12dStatement : Prop :=
  ∀ (D : Type) [Fintype D] (F : Finset D → ℝ),
    ∀ r : ℕ, ContDiff ℝ r (fun rates : D → ℝ => supportMean F rates)

/-- P5-I13, smoothness and bounded coefficients for B18. Paper label: `lem:conv-interp`; blueprint: `P5-I13`. -/
def SA_I13cStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ →
    (∀ k : Fin 3 → ℕ, 0 ≤ interpolationCoefficient q n₁ n₂ k ∧
      interpolationCoefficient q n₁ n₂ k ≤ 1) ∧
    ∀ r : ℕ, ContDiff ℝ r (chiBar q n₁ n₂)

/-- P5-I16, identification of the finite expectation with the frozen mixed law. Paper label: `lem:conv-interp`; blueprint: `P5-I16`. -/
def SA_I16dStatement : Prop :=
  ∀ q n₁ n₂ : ℕ, 1 ≤ q → 1 ≤ n₁ → 1 ≤ n₂ → ∀ c : ℝ, 0 ≤ c →
    ∀ θ : ℝ, θ ∈ Set.Icc 0 c →
    Summable (fun k : Fin 3 → ℕ =>
      (∏ i, poissonWeight (interpolationMeans n₁ n₂ c θ i) (k i)) *
        mixedGraphMean n₁ n₂ k (interpolationClassDrift q n₁ n₂)) ∧
    poissonInterpolationMean n₁ n₂ (interpolationMeans n₁ n₂ c θ)
      (interpolationClassDrift q n₁ n₂) = driftMean q n₁ n₂ c θ

/-- P5-I17 assembly: nonnegative derivative compares the endpoints. -/
theorem SA_I17_assembly (h13 : SA_I13Statement) (h16 : SA_I16Statement) :
    SA_I17Statement := by
  intro q n₁ n₂ hq h₁ h₂ c hc
  by_cases hc0 : c = 0
  · subst c
    rw [h13.2.2.1 q n₁ hq h₁, h13.2.2.1 q n₂ hq h₂,
      h13.2.2.1 q (n₁ + n₂) hq (by omega)]
    norm_num
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hd := h16.2.1 q n₁ n₂ hq h₁ h₂ c hcpos
  have hs := (h16.2.2 q n₁ n₂ hq h₁ h₂).2 c hc
  have hmono : MonotoneOn (finiteChi q n₁ n₂ c) (Set.Icc 0 c) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 c)
      (fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt)
      (fun θ hθ => (hd θ (interior_subset hθ)).hasDerivWithinAt)
      (fun θ hθ => hs θ (interior_subset hθ))
  have hle := hmono ⟨le_rfl, hc⟩ ⟨hc, le_rfl⟩ hc
  obtain ⟨he0, hec⟩ := h13.2.1 q n₁ n₂ hq h₁ h₂ c hc
  rwa [he0, hec] at hle
end ThLean.BP.SA

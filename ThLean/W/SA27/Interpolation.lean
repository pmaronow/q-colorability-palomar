import ThLean.BP.SA.Interpolation
import ThLean.Contrib.SA27.Interpolation

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA27
open ThresholdFoundations ThLean.BP.SA

private lemma uniformMean_mem_Icc_one {A : Type*} [Fintype A] [Inhabited A]
    (f : A → ℝ) (h₀ : ∀ a, 0 ≤ f a) (h₁ : ∀ a, f a ≤ 1) :
    uniformMean f ∈ Set.Icc (0 : ℝ) 1 := by
  have hc : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨default⟩)
  rw [Set.mem_Icc]
  constructor
  · unfold uniformMean
    exact div_nonneg (Finset.sum_nonneg fun a _ => h₀ a) (le_of_lt hc)
  · unfold uniformMean
    apply (div_le_iff₀ hc).2
    calc
      (∑ a, f a) ≤ (Fintype.card A : ℝ) := by
        calc
          (∑ a, f a) ≤ ∑ _a : A, (1 : ℝ) := Finset.sum_le_sum fun a _ => h₁ a
          _ = (Fintype.card A : ℝ) := by simp
      _ = 1 * (Fintype.card A : ℝ) := by ring

private lemma interpolationCoefficient_abs_le_one (q n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (k : Fin 3 → ℕ) :
    |interpolationCoefficient q n₁ n₂ k| ≤ 1 := by
  letI : Inhabited (Fin n₁) := ⟨⟨0, by omega⟩⟩
  letI : Inhabited (Fin n₂) := ⟨⟨0, by omega⟩⟩
  letI : Inhabited (Fin (n₁ + n₂)) := ⟨⟨0, by omega⟩⟩
  have hind : ∀ x₀ : Fin (k 0) → Fin (n₁ + n₂) × Fin (n₁ + n₂),
      ∀ x₁ : Fin (k 1) → Fin n₁ × Fin n₁,
        uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂))) ∈ Set.Icc (0 : ℝ) 1 := by
    intro x₀ x₁
    apply uniformMean_mem_Icc_one
    · intro x₂
      simp only [indicator]
      split_ifs <;> norm_num
    · intro x₂
      simp only [indicator]
      split_ifs <;> norm_num
  have hmid : ∀ x₀ : Fin (k 0) → Fin (n₁ + n₂) × Fin (n₁ + n₂),
      uniformMean (fun x₁ : Fin (k 1) → Fin n₁ × Fin n₁ =>
        uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂)))) ∈ Set.Icc (0 : ℝ) 1 := by
    intro x₀
    apply uniformMean_mem_Icc_one
    · intro x₁
      exact (hind x₀ x₁).1
    · intro x₁
      exact (hind x₀ x₁).2
  have hall : uniformMean (fun x₀ : Fin (k 0) → Fin (n₁ + n₂) × Fin (n₁ + n₂) =>
      uniformMean (fun x₁ : Fin (k 1) → Fin n₁ × Fin n₁ =>
        uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂))))) ∈ Set.Icc (0 : ℝ) 1 := by
    apply uniformMean_mem_Icc_one
    · intro x₀
      exact (hmid x₀).1
    · intro x₀
      exact (hmid x₀).2
  change |uniformMean (fun x₀ : Fin (k 0) → Fin (n₁ + n₂) × Fin (n₁ + n₂) =>
      uniformMean (fun x₁ : Fin (k 1) → Fin n₁ × Fin n₁ =>
        uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂)))))| ≤ 1
  rcases Set.mem_Icc.mp hall with ⟨hlo, hhi⟩
  rw [abs_le]
  constructor <;> linarith

/-- The leaf follows from its signed finite-mark count expansion and the
support-law reduction in SA-I11b. -/
theorem SA_I13aStatement_from_marked_expansion
    (h10 : SA_I10Statement) (h11a : SA_I11aStatement)
    (h11b : SA_I11bStatement)
    (hexp : ThLean.Contrib.SA27.MarkedInterpolationExpansionStatement h10 h11a) :
    SA_I13aStatement := by
  intro q n₁ n₂ hq hn₁ hn₂ μ
  have hbase : Summable (fun k : Fin 3 → ℕ =>
      (∏ i : Fin 3, poissonWeight (μ i) (k i)) * (1 : ℝ)) := by
    simpa using (h11b (Fin 3) μ (fun _ : Finset (Fin 3) => (1 : ℝ))).1
  have hs : Summable (fun k : Fin 3 → ℕ =>
      (∏ i : Fin 3, poissonWeight (μ i) (k i)) *
        interpolationCoefficient q n₁ n₂ k) := by
    apply Summable.of_norm_bounded hbase.norm
    intro k
    rw [norm_mul]
    calc
      ‖∏ i : Fin 3, poissonWeight (μ i) (k i)‖ *
          ‖interpolationCoefficient q n₁ n₂ k‖ ≤
        ‖∏ i : Fin 3, poissonWeight (μ i) (k i)‖ * 1 :=
          mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using
            interpolationCoefficient_abs_le_one q n₁ n₂ (by omega) (by omega) k)
            (norm_nonneg _)
      _ = ‖(∏ i : Fin 3, poissonWeight (μ i) (k i)) * (1 : ℝ)‖ := by simp
  let rate : InterpolationMark n₁ n₂ → ℝ := interpolationMarkRate μ
  let F : Finset (InterpolationMark n₁ n₂) → ℝ := fun T =>
    indicator (Colorable q (supportGraph interpolationMarkEdge T))
  have hmark := h11b (InterpolationMark n₁ n₂) rate F
  rcases hmark with ⟨_, hmarkeq⟩
  refine ⟨hs, ?_⟩
  change chiBar q n₁ n₂ μ = supportMean F rate
  calc
    chiBar q n₁ n₂ μ =
        ∑' z : InterpolationMark n₁ n₂ → ℕ,
          (∏ e : InterpolationMark n₁ n₂, poissonWeight (rate e) (z e)) *
            F (Finset.univ.filter (fun e => 0 < z e)) := by
      simpa [rate, F] using hexp q n₁ n₂ hq hn₁ hn₂ μ
    _ = supportMean F rate := by simpa [rate, F, supportMean] using hmarkeq

example (h10 : SA_I10Statement) (h11a : SA_I11aStatement)
    (h11b : SA_I11bStatement)
    (hexp : ThLean.Contrib.SA27.MarkedInterpolationExpansionStatement h10 h11a) :
    SA_I13aStatement := SA_I13aStatement_from_marked_expansion h10 h11a h11b hexp

end ThLean.W.SA27

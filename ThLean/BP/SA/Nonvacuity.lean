import ThLean.BP.SA.Bridges
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ThLean.BP.SA
open ThresholdFoundations

/-- A concrete admissible error sequence, independent of the graph conjecture. -/
theorem geometricError_admissible : AdmissibleError (fun n => (1 / 2 : ℝ) ^ n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n _
    exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  · intro n m _ hnm
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm
  · have hs : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
      summable_geometric_of_abs_lt_one (by norm_num)
    apply Summable.of_nonneg_of_le (fun k => by positivity) _ hs
    intro k
    have hk : k ≤ Nat.floor (Real.exp (k + 1 : ℝ)) := Nat.le_floor (by
      have he := Real.add_one_le_exp (k + 1 : ℝ)
      linarith)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk

example : ∃ g : ℝ → ℝ, (∀ u : ℝ, 1 ≤ u → 0 < g u) ∧ AnalyticError 1 g := by
  refine ⟨fun u => (1 / 2 : ℝ) ^ Nat.floor u, ?_, ?_⟩
  · intro u _; positivity
  · refine ⟨le_rfl, ?_, ?_, geometricError_admissible.2.2⟩
    · intro u _; positivity
    · intro a _ b _ hab
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.floor_mono hab)

example : Compares (fun _ => 0) (fun _ => 0) 1 := by
  refine ⟨le_rfl, ?_, ?_⟩ <;> intros <;> norm_num

example : ∃ q : ℕ, ∃ Λ η : ℝ,
    3 ≤ q ∧ gamma q + 1 < Λ ∧ 0 < η ∧ η ≤ etaZero Λ := by
  refine ⟨3, gamma 3 + 2, etaZero (gamma 3 + 2), by omega, ?_, ?_, le_rfl⟩
  · linarith
  · unfold etaZero; positivity

example : (BlockTree.node (.leaf 2) (.leaf 3)).Balanced 2 := by
  norm_num [BlockTree.Balanced, BlockTree.leaves]

example : Colorable 1 (0 : MGraph (Fin 1)) := by
  refine ⟨fun _ => 0, ?_⟩
  simp [IsColoring]

example : (∀ e : Fin 1, 0 ≤ (fun _ : Fin 1 => (0 : ℝ)) e) ∧
    (∀ e : Fin 1, 0 ≤ (fun _ : Fin 1 => (1 : ℝ)) e) := by norm_num
end ThLean.BP.SA

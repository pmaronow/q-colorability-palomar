import ThLean.BP.S6.Main
import ThLean.BP.S6.Measure

noncomputable section
open ThresholdFoundations
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S6

/-- Nonempty pair and compatible graph hypotheses, including an outside vertex. -/
example : Nonempty (Edge 3) := by
  exact ⟨⟨s((0 : Fin 3), (1 : Fin 3)), by decide⟩⟩

example : Colorable 3 (0 : Graph 3) := by
  refine ⟨fun v => v, ?_⟩
  intro a b h
  simp at h

example : (1 : Fin 3) ∉ frozenClass 3 (0 : Graph 3) 0 := by
  intro h
  have hf : Frozen 3 (0 : Graph 3) 0 1 := (Finset.mem_filter.mp h).2
  have hc : IsColoring 3 (0 : Graph 3) (fun v => v) := by
    intro a b h
    simp at h
  have he := hf.2 (fun v => v) hc
  norm_num at he

example : IsFiniteStoppingTime (fun _ : Hist 3 2 => (0 : WithTop ℕ)) := by
  intro m x y h
  rfl

example : SymmetricRelation (∅ : Finset (Fin 0 × Fin 0)) := by
  intro a b
  simp

example : SymmetricRelation ({((), ())} : Finset (Unit × Unit)) := by
  intro a b
  simp

example (M : ℕ) :
    (∀ m j : ℕ, 0 ≤ (fun _ _ => (0 : ℝ)) m j) ∧
    (∀ m j : ℕ, 1 ≤ j → j ≤ m → m < M →
      (0 : ℝ) ≤ 0 + alpha * 0) := by
  simp

/-- The analytic-cutoff premise is attained at an integer size. -/
example (Λ : ℝ) : ∃ n : ℕ, 3 ≤ n ∧ analyticCutoff Λ ≤ fourthLog n := by
  let T := analyticCutoff Λ
  let n := max 3 (Nat.ceil (Real.exp (T ^ (4 : ℕ))))
  have hT : 0 ≤ T := le_trans (by norm_num) (le_max_left _ _)
  have hn : 3 ≤ n := le_max_left _ _
  have hexp : Real.exp (T ^ (4 : ℕ)) ≤ (n : ℝ) := by
    have hc : (Nat.ceil (Real.exp (T ^ (4 : ℕ))) : ℝ) ≤ n := by
      exact_mod_cast (le_max_right 3 (Nat.ceil (Real.exp (T ^ (4 : ℕ)))))
    exact (Nat.le_ceil _).trans hc
  have hlog : T ^ (4 : ℕ) ≤ Real.log (n : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hexp
  have hr := Real.rpow_le_rpow (pow_nonneg hT 4) hlog
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have heq : Real.rpow (T ^ (4 : ℕ)) ((1 : ℝ) / 4) = T := by
    simpa using (Real.rpow_natCast_mul hT 4 ((1 : ℝ) / 4)).symm
  change Real.rpow (T ^ (4 : ℕ)) ((1 : ℝ) / 4) ≤ fourthLog n at hr
  rw [heq] at hr
  exact ⟨n, hn, hr⟩

end ThLean.BP.S6

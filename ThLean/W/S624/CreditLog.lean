module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import ThLean.BP.S6.Credit

@[expose] public section

noncomputable section

namespace ThLean.W.S624

theorem S6_23Statement_holds : ThLean.BP.S6.S6_23Statement := by
  constructor
  · exact Real.log_pos (by norm_num)
  · intro z hz
    by_cases hz1 : z ≤ 1
    · have hconc := strictConcaveOn_log_Ioi.concaveOn
      have h := hconc.2 (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
        (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
        (sub_nonneg.mpr hz1) hz (by ring : (1 - z) + z = (1 : ℝ))
      have h' : z * Real.log 2 ≤ Real.log (1 - z + z * 2) := by
        simpa [Real.log_one, smul_eq_mul] using h
      rw [min_eq_left hz1]
      calc
        Real.log 2 * z = z * Real.log 2 := by ring
        _ ≤ Real.log (1 - z + z * 2) := h'
        _ = Real.log (1 + z) := by
          congr 1
          ring
    · have hlog : Real.log 2 ≤ Real.log (1 + z) :=
        Real.log_le_log (by norm_num) (by linarith)
      rw [min_eq_right (le_of_lt (lt_of_not_ge hz1))]
      simpa using hlog

end ThLean.W.S624

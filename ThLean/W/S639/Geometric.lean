module

public import ThLean.BP.S6.Analytic

@[expose] public section

noncomputable section
open scoped BigOperators
open ThLean.BP.S6

namespace ThLean.W.S639

theorem S6_36Statement_holds : ThLean.BP.S6.S6_36Statement := by
  intro r L
  have hαnonneg : 0 ≤ alpha := by norm_num [alpha]
  have hden : 0 < 1 - alpha := by norm_num [alpha]
  have hinv : (1 - alpha)⁻¹ = (4 / 3 : ℝ) := by norm_num [alpha]
  have hgeom : (∑ s ∈ Finset.range L, alpha ^ s) ≤ (4 / 3 : ℝ) := by
    have hformula : (∑ s ∈ Finset.range L, alpha ^ s) =
        (1 - alpha ^ L) / (1 - alpha) := by
      calc
        (∑ s ∈ Finset.range L, alpha ^ s) =
            (alpha ^ L - 1) / (alpha - 1) := geom_sum_eq (by norm_num [alpha]) L
        _ = (1 - alpha ^ L) / (1 - alpha) := by
          rw [← neg_div_neg_eq]
          simp
    rw [hformula]
    calc
      (1 - alpha ^ L) / (1 - alpha) ≤ 1 / (1 - alpha) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hden)
        have hpow : 0 ≤ alpha ^ L := pow_nonneg hαnonneg L
        linarith
      _ = (4 / 3 : ℝ) := by rw [← hinv]; simp
  refine ⟨?_, hgeom, ?_⟩
  · have hfactor : (∑ s ∈ Finset.range L, alpha ^ (r + s)) =
        alpha ^ r * (∑ s ∈ Finset.range L, alpha ^ s) := by
      simp_rw [pow_add]
      rw [← Finset.mul_sum]
    calc
      (∑ s ∈ Finset.range L, alpha ^ (r + s)) =
          alpha ^ r * (∑ s ∈ Finset.range L, alpha ^ s) := hfactor
      _ ≤ alpha ^ r * (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hgeom (pow_nonneg hαnonneg r)
      _ = (4 / 3 : ℝ) * alpha ^ r := by ring
  · intro s
    exact pow_nonneg hαnonneg s

end ThLean.W.S639

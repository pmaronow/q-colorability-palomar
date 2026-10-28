import ThLean.BP.S3.Poisson

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ThLean.W.S346

open ThLean.BP.S3
open ThresholdFoundations

theorem S3_40Statement_of_deps (hG : S3_40GStatement) : S3_40Statement := by
  intro p m hp
  let f : ℝ → ℝ := fun s => s ^ m * Real.exp (-s)
  let c : ℝ := 1 / (m.factorial : ℝ)
  have hfac : (m.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hbase_int : IntegrableOn f (Ioi 0) := (hG m).1
  have hbase0 : IntegrableOn f (Ioi (p * 0)) := by
    simpa using hbase_int
  have hscaled_int : IntegrableOn (fun t : ℝ => f (p * t)) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff f 0 hp).2 hbase0
  have hkernel_eq : (fun t : ℝ => poissonWeight (p * t) m) =
      (fun t : ℝ => c * f (p * t)) := by
    funext t
    simp only [poissonWeight, f, c]
    field_simp [hfac]
  have hsub : (∫ t : ℝ in Ioi 0, f (p * t)) =
      (1 / p) * (∫ s : ℝ in Ioi 0, f s) := by
    rw [integral_comp_mul_left_Ioi f 0 hp]
    simp [smul_eq_mul, f]
  constructor
  · rw [hkernel_eq]
    exact hscaled_int.const_mul c
  · calc
      (∫ t : ℝ in Ioi 0, poissonWeight (p * t) m)
          = ∫ t : ℝ in Ioi 0, c * f (p * t) := by rw [hkernel_eq]
      _ = c * (∫ t : ℝ in Ioi 0, f (p * t)) := by rw [integral_const_mul]
      _ = c * ((1 / p) * (∫ s : ℝ in Ioi 0, f s)) := by rw [hsub]
      _ = 1 / p := by
        rw [(hG m).2.2]
        simp only [c]
        field_simp [hfac, hp.ne']

example (hG : S3_40GStatement) : S3_40Statement :=
  S3_40Statement_of_deps hG

end ThLean.W.S346

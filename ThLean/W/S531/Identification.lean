module

public import ThLean.BP.S5.Identification
public import ThLean.BP.S5.Elementary

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology ENNReal

namespace ThLean.W.S531

open ThLean.BP.S5
open ThresholdFoundations

/-- The finite occupation integral splits at the low-time cutoff. -/
theorem S5_26CStatement_of_deps
    (h17B : S5_17BStatement) (h17C : S5_17CStatement)
    (_hE08 : S5_E08Statement) :
    S5_26CStatement := by
  intro q N D hq hqN hD hDN
  have h17b := h17B q N D hq hqN hD hDN
  have h17c := h17C q N D hq hqN hD hDN
  refine ⟨h17b.2.1, ?_⟩
  rcases h17c with ⟨hint, hrepr⟩
  rw [← hrepr]
  let f : ℝ → ℝ := discrepancy q N D
  change (∫ s in Set.Ici (0 : ℝ), f s) =
    (∫ s in (0 : ℝ)..lowTimeCap q N, f s) +
      ∫ s in Set.Ici (lowTimeCap q N), f s
  have hcap : 0 ≤ lowTimeCap q N := by
    unfold lowTimeCap
    have hqone : 1 ≤ q := by omega
    have hqoneR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqone
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqoneR
    positivity
  have hIoi0 : IntegrableOn f (Set.Ioi (0 : ℝ)) :=
    hint.mono_set (by
      intro x hx
      exact (Set.mem_Ioi.mp hx).le)
  have hIoiCap : IntegrableOn f (Set.Ioi (lowTimeCap q N)) :=
    hint.mono_set (by
      intro x hx
      exact le_trans hcap (Set.mem_Ioi.mp hx).le)
  calc
    (∫ s in Set.Ici (0 : ℝ), f s)
        = ∫ s in Set.Ioi (0 : ℝ), f s := integral_Ici_eq_integral_Ioi
    _ = (∫ s in (0 : ℝ)..lowTimeCap q N, f s) +
          ∫ s in Set.Ioi (lowTimeCap q N), f s :=
        (intervalIntegral.integral_interval_add_Ioi hIoi0 hIoiCap).symm
    _ = (∫ s in (0 : ℝ)..lowTimeCap q N, f s) +
          ∫ s in Set.Ici (lowTimeCap q N), f s := by
        rw [← integral_Ici_eq_integral_Ioi]

example (h17B : S5_17BStatement) (h17C : S5_17CStatement)
    (hE08 : S5_E08Statement) : ThLean.BP.S5.S5_26CStatement :=
  S5_26CStatement_of_deps h17B h17C hE08

end ThLean.W.S531

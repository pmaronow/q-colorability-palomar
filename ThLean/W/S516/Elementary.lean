import ThLean.BP.S5.Elementary

noncomputable section
open Filter

namespace ThLean.W.S516

/-- The iterated logarithm is eventually in the positive domain, and the
logarithmic ratio tends to zero there. -/
theorem S5_E10Statement_holds : ThLean.BP.S5.S5_E10Statement := by
  intro A hA
  let u : ℕ → ℝ := fun n => Real.log (Real.log n)
  have hu : Tendsto u atTop atTop := by
    dsimp [u]
    exact Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogu : Tendsto (fun n : ℕ => Real.log (u n) / u n) atTop (nhds 0) :=
    hlog.comp hu
  have hconst : Tendsto (fun n : ℕ => Real.log A / u n) atTop (nhds 0) :=
    Tendsto.const_div_atTop hu (Real.log A)
  have hsum : Tendsto (fun n : ℕ => Real.log A / u n + Real.log (u n) / u n)
      atTop (nhds 0) := by
    simpa using hconst.add hlogu
  have heq : (fun n : ℕ => Real.log (A * u n) / u n) =ᶠ[atTop]
      (fun n => Real.log A / u n + Real.log (u n) / u n) := by
    filter_upwards [hu.eventually_gt_atTop 0] with n hn
    rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hn), add_div]
  have hratio : Tendsto (fun n : ℕ => Real.log (A * u n) / u n) atTop (nhds 0) :=
    Tendsto.congr' heq.symm hsum
  have hfinal : (fun n : ℕ => if n < 16 then 0 else
      Real.log (A * Real.log (Real.log n)) / Real.log (Real.log n)) =ᶠ[atTop]
      (fun n => Real.log (A * u n) / u n) := by
    filter_upwards [eventually_ge_atTop (16 : ℕ)] with n hn
    simp [u, Nat.not_lt.mpr hn]
  exact Tendsto.congr' hfinal.symm hratio

example : ThLean.BP.S5.S5_E10Statement := S5_E10Statement_holds

end ThLean.W.S516

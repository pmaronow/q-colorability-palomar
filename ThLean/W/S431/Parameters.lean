import ThLean.BP.S4.Parameters

noncomputable section
open Filter
open scoped Topology

namespace ThLean.W.S431
open ThresholdFoundations

/-- The prescribed logarithmic error tends to zero, while its product with n
    diverges. The final clause records the integer endpoint absorption used by
    the window argument. -/
theorem S4_PAR_06Statement_holds : ThLean.BP.S4.S4_PAR_06Statement := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heps : Tendsto (fun n : ℕ => epsilon n) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (y := (3 : ℝ) / 2) (by norm_num)).comp hlog |>.congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    rw [epsilon, ite_eq_right (Nat.not_lt.mpr hn)]
    rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring]
    rfl
  have hratio : Tendsto (fun x : ℝ => Real.log x ^ ((3 : ℝ) / 2) / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (r := (3 : ℝ) / 2) (s := 1) (by norm_num)).tendsto_div_nhds_zero
  have hratioN : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ ((3 : ℝ) / 2) / (n : ℝ)) atTop (𝓝 0) := by
    exact hratio.comp tendsto_natCast_atTop_atTop
  have hratioNpos : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ ((3 : ℝ) / 2) / (n : ℝ))
      atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hratioN ?_
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hn)
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn'
    exact div_pos (Real.rpow_pos_of_pos hlogn _) (by exact_mod_cast (Nat.zero_lt_of_lt hn))
  have hprod : Tendsto (fun n : ℕ => (n : ℝ) * epsilon n) atTop atTop := by
    have hinv := hratioNpos.inv_tendsto_nhdsGT_zero
    refine hinv.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hnreal : (n : ℝ) ≠ 0 := by positivity
    have hlogpos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hn)
    have heps_eq : epsilon n = (Real.log (n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
      simp only [epsilon, ite_eq_right (Nat.not_lt.mpr hn)]
      rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring]
      exact Real.rpow_neg (le_of_lt hlogpos) _
    change ((Real.log (n : ℝ) ^ ((3 : ℝ) / 2) / (n : ℝ))⁻¹ =
      (n : ℝ) * epsilon n)
    rw [heps_eq]
    field_simp [hnreal]
  refine ⟨heps, hprod, ?_⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (hprod.eventually_ge_atTop 1)
  refine ⟨max 3 N₀, le_max_left _ _, ?_⟩
  intro n hn
  exact hN₀ n (le_trans (le_max_right _ _) hn)

end ThLean.W.S431

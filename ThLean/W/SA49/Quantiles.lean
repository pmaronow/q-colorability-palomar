import ThLean.BP.SA.Convergence

set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA49

open ThresholdFoundations
open ThLean.BP.SA

private theorem rho_adjacent_product
    (h13b : SA_I13bStatement) (h16b : SA_I16bStatement)
    (h16c : SA_I16cStatement)
    (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) (c : ℝ) (hc : 0 < c) :
    rho q n c * Real.exp (-c) ≤ rho q (n + 1) c := by
  have hd := h16b q n 1 hq hn (by omega) c hc
  have hs := (h16c q n 1 hq hn (by omega)).2 c hc.le
  have hmono : MonotoneOn (finiteChi q n 1 c) (Set.Icc 0 c) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 c)
      (fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt)
      (fun θ hθ => (hd θ (interior_subset hθ)).hasDerivWithinAt)
      (fun θ hθ => hs θ (interior_subset hθ))
  have hle := hmono ⟨le_rfl, hc.le⟩ ⟨hc.le, le_rfl⟩ hc.le
  have hend := h13b.1 q n 1 hq hn (by omega) c hc.le
  rw [hend.1, hend.2] at hle
  rw [h13b.2.2 q hq c hc.le] at hle
  exact hle

theorem SA_Q27Statement_of_deps
    (h13b : SA_I13bStatement)
    (h16b : SA_I16bStatement)
    (h16c : SA_I16cStatement)
    (h22a : SA_Q22aStatement)
    (h25 : SA_Q25Statement)
    (h23a : SA_Q23aStatement)
    (h23b : SA_Q23bStatement)
    (hF01 : SA_F01Statement)
    (hC60a : SA_C60aStatement) : SA_Q27Statement := by
  intro q hq Λ η K δ n₁ s₀ hΛ hδ hη hη₀ hw hcut a ha
  have hcut0 := hcut.1
  have h2q_s : 2 * q ≤ s₀ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hcut0)
  have hn₁_s : n₁ ≤ s₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hcut0)
  have h2q_a : 2 * q ≤ a := le_trans h2q_s ha
  have hn₁_a : n₁ ≤ a := le_trans hn₁_s ha
  have hqpos : 1 ≤ q := by omega
  have hapos : 1 ≤ a := by omega
  have hF := hF01 q hq
  have hFΛ := hF.2.2 Λ hΛ
  have hηlt : η < (1 / 8 : ℝ) := lt_of_le_of_lt hη₀ hFΛ.2.2.1
  have hηhalf : η ≤ (1 / 2 : ℝ) := by linarith
  have hxi := hC60a q hq Λ η hΛ hη hηhalf a h2q_a
  have hcut_a := hcut.2 a ha
  have hxi_lower : (1 / 4 : ℝ) < xi q Λ η a := hcut_a.2.1
  have hdev_small : 2 * (poissonDeviation a : ℝ) / a < (1 / 4 : ℝ) :=
    hcut_a.2.2.1
  let c : ℝ := xi q Λ η a - 2 * (poissonDeviation a : ℝ) / a
  have hc : 0 < c := by dsimp [c]; linarith
  have hdev_nonneg : 0 ≤ (poissonDeviation a : ℝ) / a :=
    (h23b.1 a hapos).1
  have hcΛ : c ≤ Λ := by
    dsimp [c]
    have hxiΛ : xi q Λ η a ≤ Λ := hxi.2
    have hdevterm : 0 ≤ 2 * (poissonDeviation a : ℝ) / a := by positivity
    linarith
  have htail_a : poissonTailError Λ a ≤ η := by
    exact le_trans (hcut_a.2.2.2) (min_le_left _ _)
  have htail_small : poissonTailError Λ a ≤ (1 / 8 : ℝ) := by
    exact le_trans (hcut_a.2.2.2) (min_le_right _ _)
  have hLidentity : c * (a : ℝ) = (lowerLocation q Λ η a : ℝ) -
      2 * (poissonDeviation a : ℝ) := by
    dsimp [c, xi]
    field_simp
  have hlow_arg : c * ((a : ℝ) - 1) ≤
      (lowerLocation q Λ η a : ℝ) - poissonDeviation a := by
    rw [show ((a : ℝ) - 1) = (a : ℝ) - 1 by rfl]
    calc
      c * ((a : ℝ) - 1) = c * (a : ℝ) - c := by ring
      _ ≤ c * (a : ℝ) := by linarith
      _ = (lowerLocation q Λ η a : ℝ) - 2 * (poissonDeviation a : ℝ) := hLidentity
      _ ≤ (lowerLocation q Λ η a : ℝ) - poissonDeviation a := by
        have : 0 ≤ (poissonDeviation a : ℝ) := Nat.cast_nonneg _
        linarith
  have hrho_lower := h22a q a hq h2q_a Λ η c hΛ hη hηhalf hc hcΛ hlow_arg
  have hEpos : 0 < Real.exp (-Λ) := Real.exp_pos _
  have htail_factor : (7 / 8 : ℝ) ≤ 1 - poissonTailError Λ a := by
    linarith
  have heta_factor : (7 / 8 : ℝ) ≤ 1 - η := by linarith
  have hfactor : (7 / 8 : ℝ) ^ 2 ≤ (1 - η) * (1 - poissonTailError Λ a) := by
    calc
      (7 / 8 : ℝ) ^ 2 = (7 / 8 : ℝ) * (7 / 8 : ℝ) := by ring
      _ ≤ (1 - η) * (1 - poissonTailError Λ a) :=
        mul_le_mul heta_factor htail_factor (by norm_num) (by linarith)
  have hrho_bound : Real.exp (-Λ) * ((7 / 8 : ℝ) ^ 2) ≤ rho q a c := by
    calc
      Real.exp (-Λ) * ((7 / 8 : ℝ) ^ 2) ≤
          Real.exp (-Λ) * ((1 - η) * (1 - poissonTailError Λ a)) :=
        mul_le_mul_of_nonneg_left hfactor hEpos.le
      _ ≤ rho q a c := by nlinarith [hrho_lower]
  have hexp_cmp : Real.exp (-Λ) ≤ Real.exp (-c) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod_lower : Real.exp (-2 * Λ) / 2 < rho q a c * Real.exp (-c) := by
    have hEEpos : 0 < Real.exp (-Λ) * Real.exp (-Λ) := mul_pos hEpos hEpos
    have hEid : Real.exp (-Λ) * Real.exp (-Λ) = Real.exp (-2 * Λ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hrat : (1 / 2 : ℝ) < (7 / 8 : ℝ) ^ 2 := by norm_num
    have hstep1 : Real.exp (-2 * Λ) / 2 <
        (Real.exp (-Λ) * ((7 / 8 : ℝ) ^ 2)) * Real.exp (-Λ) := by
      rw [← hEid]
      nlinarith [mul_pos hEEpos (sub_pos.mpr hrat)]
    have hstep2 : (Real.exp (-Λ) * ((7 / 8 : ℝ) ^ 2)) * Real.exp (-Λ) ≤
        (Real.exp (-Λ) * ((7 / 8 : ℝ) ^ 2)) * Real.exp (-c) :=
      mul_le_mul_of_nonneg_left hexp_cmp (by positivity)
    have hstep3 : (Real.exp (-Λ) * ((7 / 8 : ℝ) ^ 2)) * Real.exp (-c) ≤
        rho q a c * Real.exp (-c) :=
      mul_le_mul_of_nonneg_right hrho_bound (by positivity)
    exact lt_of_lt_of_le hstep1 (le_trans hstep2 hstep3)
  have hprod := rho_adjacent_product h13b h16b h16c q a hqpos hapos c hc
  have hcut_next := hcut.2 (a + 1) (by omega)
  have htail_next : poissonTailError Λ (a + 1) ≤ η := by
    exact le_trans hcut_next.2.2.2 (min_le_left _ _)
  have hqnext : 2 * q ≤ a + 1 := by omega
  have hqa : n₁ ≤ a + 1 := by omega
  have h25result := h25 q (a + 1) hq hqnext Λ η K c δ n₁ hΛ hδ hη hη₀ hw hqa hc hcΛ
    hcut_next.1 htail_next (lt_of_lt_of_le hprod_lower hprod)
  have hxi_next := h25result.2
  have hdev_next := (h23b.1 (a + 1) (by omega)).2
  have hdev_a := (h23b.1 a hapos).2
  have hdev_next_real : (poissonDeviation (a + 1) : ℝ) / (a + 1 : ℝ) ≤
      envelope (a + 1 : ℝ) + 1 / (a + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdev_next
  have ha_exp2 : Real.exp 2 ≤ (a : ℝ) := by
    have hceil : Nat.ceil (Real.exp 2) ≤ a :=
      le_trans (le_max_right _ _) (le_trans hcut0 ha)
    have hceil_real : Real.exp 2 ≤ (Nat.ceil (Real.exp 2) : ℝ) := by
      exact_mod_cast Nat.le_ceil (Real.exp 2)
    exact le_trans hceil_real (by exact_mod_cast hceil)
  have ha1_exp2 : Real.exp 2 ≤ (a + 1 : ℝ) := by
    have : (a : ℝ) ≤ (a + 1 : ℝ) := by norm_num
    exact le_trans ha_exp2 this
  have henv_mono := h23a.2.1
  have henvnext : envelope (a + 1 : ℝ) ≤ envelope (a : ℝ) :=
    henv_mono (Set.mem_Ici.mpr ha_exp2) (Set.mem_Ici.mpr ha1_exp2) (by norm_num)
  have henvsum_mono := h23a.2.2.1
  have henvsum_next : envelope (a + 1 : ℝ) + 1 / (a + 1 : ℝ) ≤
      envelope (a : ℝ) + 1 / (a : ℝ) :=
    henvsum_mono (Set.mem_Ici.mpr ha_exp2) (Set.mem_Ici.mpr ha1_exp2) (by norm_num)
  have hdev_next_bound : (poissonDeviation (a + 1) : ℝ) / (a + 1 : ℝ) ≤
      envelope (a : ℝ) + 1 / (a : ℝ) := by
    exact le_trans hdev_next_real henvsum_next
  have henv_floor : (1 : ℝ) / (a : ℝ) ≤ envelope (a : ℝ) :=
    h23a.2.2.2.2.2 (a : ℝ) (by
      have : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      exact le_trans this ha_exp2)
  have hΛpos : 0 < Λ := hFΛ.1
  have hΛdiv : Λ / (a + 1 : ℝ) ≤ Λ / (a : ℝ) := by
    exact div_le_div_of_nonneg_left hΛpos.le (by positivity)
      (by norm_num : (a : ℝ) ≤ (a + 1 : ℝ))
  have hδmono : δ (a + 1) ≤ δ a := (hδ.2.1 a (a + 1) hapos (by omega))
  have hKδ : K * δ (a + 1) ≤ K * δ a := mul_le_mul_of_nonneg_left hδmono hw.1.le
  have hΛsmall : Λ / (a : ℝ) ≤ Λ * envelope (a : ℝ) := by
    have := mul_le_mul_of_nonneg_left henv_floor hΛpos.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hdelta_dev_a : 2 * (poissonDeviation a : ℝ) / a ≤
      2 * (envelope (a : ℝ) + 1 / (a : ℝ)) := by
    calc
      2 * (poissonDeviation a : ℝ) / a =
          2 * ((poissonDeviation a : ℝ) / a) := by ring
      _ ≤ 2 * (envelope (a : ℝ) + 1 / (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hdev_a (by norm_num)
  have hcomp :
      xi q Λ η a - comparisonError δ Λ K a ≤
        c - Λ / (a + 1 : ℝ) - K * δ (a + 1) -
          (poissonDeviation (a + 1) : ℝ) / (a + 1 : ℝ) := by
    have hδa : stepExtension δ (a : ℝ) = δ a := by
      simp [stepExtension]
    have herror : comparisonError δ Λ K (a : ℝ) =
        K * δ a + (Λ + 6) * envelope (a : ℝ) := by
      simp [comparisonError, hδa, envelope]
      ring
    rw [herror]
    dsimp [c]
    have hbound := hdelta_dev_a
    have h1over : (1 : ℝ) / (a : ℝ) ≤ envelope (a : ℝ) := henv_floor
    nlinarith [hdev_next_bound, hΛdiv, hKδ, hΛsmall]
  have hxi_next_real :
      c - Λ / (a + 1 : ℝ) - K * δ (a + 1) -
        (poissonDeviation (a + 1) : ℝ) / (a + 1 : ℝ) < xi q Λ η (a + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hxi_next
  exact le_of_lt (lt_of_le_of_lt hcomp hxi_next_real)

end ThLean.W.SA49

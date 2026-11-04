module

public import ThLean.BP.SA.Basics
public import ThLean.BP.SA.Quantiles

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace ThLean.W.SA46

open ThresholdFoundations
open ThLean.BP.SA

theorem SA_Q24Statement_of_deps
    (hQ23b : SA_Q23bStatement)
    (hF01 : SA_F01Statement)
    (hCentre : PreCentreStatement) :
    SA_Q24Statement := by
  intro q hq Λ η hΛ hη hηZero n₁
  have hF := hF01 q hq
  have hΛfacts := hF.2.2 Λ hΛ
  have hηHalf : η ≤ (1 / 2 : ℝ) := by
    exact hηZero.trans <| le_of_lt <| lt_trans hΛfacts.2.2.1 hΛfacts.2.2.2

  have hCentreFacts := hCentre q hq Λ hΛ η hη hηHalf
  have hUpperEventually :
      ∀ᶠ n : ℕ in atTop,
        upperLocation q Λ η n < cap Λ n := by
    filter_upwards [hCentreFacts.2.1 (gamma q + 1) (by linarith)] with n hn
    exact hn.2.2

  have hXiRaw :
      ∀ᶠ n : ℕ in atTop,
        (1 / 4 : ℝ) * (n : ℝ) < (lowerLocation q Λ η n : ℝ) := by
    obtain ⟨C, hC, hBound, hEventually⟩ :=
      hCentreFacts.2.2 (1 / 4 : ℝ) (by norm_num) (by norm_num)
    exact hEventually

  have hXiEventually :
      ∀ᶠ n : ℕ in atTop,
        (1 / 4 : ℝ) < xi q Λ η n := by
    filter_upwards [hXiRaw, Filter.eventually_gt_atTop (0 : ℕ)] with n hn hpos
    have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    change (1 / 4 : ℝ) < (lowerLocation q Λ η n : ℝ) / (n : ℝ)
    rw [lt_div_iff₀ hnReal]
    exact hn

  have hEnvelopeLimit :
      Tendsto (fun n : ℕ => envelope (n : ℝ)) atTop (𝓝 0) := by
    have hLittleO :
        Real.log =o[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
      isLittleO_log_rpow_atTop (by norm_num)
    have hRealLimit :
        Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      hLittleO.tendsto_div_nhds_zero
    have hNatLimit := hRealLimit.comp tendsto_natCast_atTop_atTop
    change Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0)
      at hNatLimit
    simpa [envelope, Real.sqrt_eq_rpow] using hNatLimit

  have hInvLimit :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have hNatLimit :
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    change Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) at hNatLimit
    simpa only [one_div] using hNatLimit
  have hErrorLimit :
      Tendsto (fun n : ℕ => envelope (n : ℝ) + 1 / (n : ℝ)) atTop (𝓝 0) :=
    by simpa using hEnvelopeLimit.add hInvLimit
  have hErrorEventually :
      ∀ᶠ n : ℕ in atTop,
        envelope (n : ℝ) + 1 / (n : ℝ) < (1 / 8 : ℝ) :=
    hErrorLimit.eventually (Iio_mem_nhds (by norm_num))

  have hDeviationEventually :
      ∀ᶠ n : ℕ in atTop,
        2 * (poissonDeviation n : ℝ) / (n : ℝ) < (1 / 4 : ℝ) := by
    filter_upwards [hErrorEventually, Filter.eventually_ge_atTop (1 : ℕ)] with n hError hn
    have hDeviation := hQ23b.1 n (by omega)
    have hScaled :
        2 * ((poissonDeviation n : ℝ) / (n : ℝ)) < (1 / 4 : ℝ) := by
      nlinarith [hDeviation.2, hError]
    calc
      2 * (poissonDeviation n : ℝ) / (n : ℝ) =
          2 * ((poissonDeviation n : ℝ) / (n : ℝ)) := by ring
      _ < (1 / 4 : ℝ) := hScaled

  have hTailEventually :
      ∀ᶠ n : ℕ in atTop,
        poissonTailError Λ n ≤ min η (1 / 8 : ℝ) := by
    have hTailLimit := hQ23b.2 Λ hΛfacts.1
    have hmin : 0 < min η (1 / 8 : ℝ) := lt_min hη (by norm_num)
    filter_upwards [hTailLimit.eventually (Iio_mem_nhds hmin)] with n hn
    exact hn.le

  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        upperLocation q Λ η n < cap Λ n ∧
          (1 / 4 : ℝ) < xi q Λ η n ∧
          2 * (poissonDeviation n : ℝ) / n < (1 / 4 : ℝ) ∧
          poissonTailError Λ n ≤ min η (1 / 8 : ℝ) := by
    filter_upwards [hUpperEventually, hXiEventually, hDeviationEventually,
      hTailEventually] with n hu hx hd ht
    exact ⟨hu, hx, hd, ht⟩

  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  refine ⟨max (max (max (2 * q) n₁) (Nat.ceil (Real.exp 2))) N, ?_, ?_⟩
  · exact le_max_left _ _
  · intro n hn
    have hNn : N ≤ n := le_trans (le_max_right _ _) hn
    exact hN n hNn

example (hQ23b : SA_Q23bStatement) (hF01 : SA_F01Statement)
    (hCentre : PreCentreStatement) : SA_Q24Statement :=
  SA_Q24Statement_of_deps hQ23b hF01 hCentre

end ThLean.W.SA46

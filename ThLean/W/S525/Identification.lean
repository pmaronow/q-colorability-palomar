module

public import ThLean.BP.S5.Identification

@[expose] public section

noncomputable section
open scoped BigOperators

namespace ThLean.W.S525
open ThresholdFoundations ThLean.BP.S5

private lemma onset_gt_two_mul (q : ℕ) (hq : 3 ≤ q) :
    2 * q < lowSizeOnset q := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hlog : 1 < Real.log (q : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hqpos]
    exact lt_of_lt_of_le Real.exp_one_lt_three hqR
  have hqcast : (0 : ℝ) < q := by positivity
  have hbase : (2 * q : ℝ) < 4 * q * Real.log (q : ℝ) := by
    nlinarith
  have hceil : 4 * (q : ℝ) * Real.log (q : ℝ) ≤ (Nat.ceil (4 * (q : ℝ) * Real.log (q : ℝ)) : ℝ) :=
    Nat.le_ceil _
  have hsize : (2 * q : ℝ) < (lowSizeOnset q : ℝ) := by
    unfold lowSizeOnset
    push_cast
    linarith
  exact_mod_cast hsize

theorem S5_22Statement_holds : S5_22Statement := by
  intro q N D hq hN hD hDN
  have hOnset := onset_gt_two_mul q hq
  have h2qN : 2 * q < N := lt_of_lt_of_le hOnset hN
  have hN2 : 2 ≤ N := by omega
  have hDle : D ≤ N := by omega
  have hND2 : 2 ≤ N - D := by omega
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hlog : 1 < Real.log (q : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hqpos]
    exact lt_of_lt_of_le Real.exp_one_lt_three hqR
  have hlogpos : 0 < Real.log (q : ℝ) := by linarith
  have hNnat : 0 < N := by omega
  have hNcast : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hNsub : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hDcast : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hMnat : 0 < N - D := by omega
  have hMcast : (0 : ℝ) < (N - D : ℕ) := by exact_mod_cast hMnat
  have hchooseN : 0 < (N.choose 2 : ℝ) := by
    exact_mod_cast (Nat.choose_pos (show 2 ≤ N by omega))
  have hchooseM : 0 < (((N - D) + 1).choose 2 : ℝ) := by
    exact_mod_cast (Nat.choose_pos (show 2 ≤ N - D + 1 by omega))
  have hrate : 0 < lowEdgeRate N := by
    unfold lowEdgeRate
    exact one_div_pos.mpr hchooseN
  have haug : 0 < augmentedRate N D := by
    unfold augmentedRate
    exact mul_pos hrate hchooseM
  have htime : 0 < lowTimeCap q N := by
    unfold lowTimeCap
    positivity
  have hMcastEq : ((N - D : ℕ) : ℝ) = (N : ℝ) - D := by
    exact Nat.cast_sub hDle
  have hchooseNform : (N.choose 2 : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 :=
    Nat.cast_choose_two (K := ℝ) N
  have hchooseMform : (((N - D) + 1).choose 2 : ℝ) =
      ((N - D : ℕ) : ℝ) * (((N - D : ℕ) : ℝ) + 1) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hrecip : 1 / augmentedRate N D =
      ((N : ℝ) * ((N : ℝ) - 1)) /
        (((N - D : ℕ) : ℝ) * ((N - D : ℕ) + 1)) := by
    rw [augmentedRate, lowEdgeRate, hchooseNform, hchooseMform]
    rw [hMcastEq]
    have hNm1 : (N : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    have hM0 : (N : ℝ) - D ≠ 0 := ne_of_gt (by exact_mod_cast hMnat)
    field_simp [hNm1, hM0]
  have hMbound : (3 / 4 : ℝ) * N ≤ (N - D : ℕ) := by
    have hDNcast : (4 : ℝ) * D ≤ N := by exact_mod_cast hDN
    rw [hMcastEq]
    nlinarith
  have hrecipBound : 1 / augmentedRate N D ≤ (16 / 9 : ℝ) := by
    rw [hrecip]
    have hden : 0 < ((N - D : ℕ) : ℝ) * ((N - D : ℕ) + 1) := by positivity
    rw [div_le_iff₀ hden]
    have hNm : (0 : ℝ) ≤ N := by positivity
    have hMnonneg : (0 : ℝ) ≤ (N - D : ℕ) := by positivity
    nlinarith [sq_nonneg ((N : ℝ) - 1), sq_nonneg (((N - D : ℕ) : ℝ) - (3 / 4 : ℝ) * N)]
  have h16 : (16 / 9 : ℝ) < 2 := by norm_num
  have hmean : ∀ s : ℝ, 0 ≤ s → s ≤ lowTimeCap q N →
      0 ≤ neighborMean N D s ∧ neighborMean N D s ≤ lowMeanBound q := by
    intro s hs0 hsCap
    have hMle : (N - D : ℕ) ≤ N - 1 := by omega
    have hMleCast : ((N - D : ℕ) : ℝ) ≤ (N : ℝ) - 1 := by
      calc
        ((N - D : ℕ) : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast hMle
        _ = (N : ℝ) - 1 := by
          simpa using Nat.cast_sub (R := ℝ) (m := 1) (n := N) (by omega)
    have hfactor : 0 ≤ lowEdgeRate N * ((N - D : ℕ) : ℝ) := by positivity
    constructor
    · unfold neighborMean
      exact mul_nonneg (mul_nonneg hrate.le (by exact_mod_cast hMnat.le)) hs0
    · have hupper : lowEdgeRate N * ((N - D : ℕ) : ℝ) * s ≤
          lowEdgeRate N * ((N : ℝ) - 1) * lowTimeCap q N := by
        have hNmin : (0 : ℝ) < (N : ℝ) - 1 := by linarith
        have hsCap' : s ≤ 2 * q * Real.log (q : ℝ) * N := by
          simpa [lowTimeCap] using hsCap
        have hcore : ((N - D : ℕ) : ℝ) * s ≤ ((N : ℝ) - 1) *
            (2 * q * Real.log (q : ℝ) * N) := by
          exact mul_le_mul hMleCast hsCap' hs0 (le_of_lt hNmin)
        have hrate' : 0 ≤ lowEdgeRate N := hrate.le
        calc
          lowEdgeRate N * ((N - D : ℕ) : ℝ) * s =
              lowEdgeRate N * (((N - D : ℕ) : ℝ) * s) := by ring
          _ ≤ lowEdgeRate N * (((N : ℝ) - 1) * (2 * q * Real.log (q : ℝ) * N)) :=
            mul_le_mul_of_nonneg_left hcore hrate'
          _ = lowEdgeRate N * ((N : ℝ) - 1) * lowTimeCap q N := by
            simp [lowTimeCap]
            ring
      have hsimple : lowEdgeRate N * ((N : ℝ) - 1) * lowTimeCap q N =
          4 * q * Real.log (q : ℝ) := by
        unfold lowEdgeRate lowTimeCap
        rw [Nat.cast_choose_two]
        have hnm1 : (N : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
        field_simp
        ring
      unfold neighborMean lowMeanBound
      rw [← hsimple]
      linarith
  exact ⟨hOnset, h2qN, hDle, hND2, hrate, haug, htime, hrecip,
    hrecipBound, h16, hmean⟩

end ThLean.W.S525

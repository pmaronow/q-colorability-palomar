import ThLean.BP.S5.Main

noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S532

/-- Eventual low-size conditions, given the two asymptotic sibling nodes. -/
theorem S5_35Statement_of_deps
    (hE09 : ThLean.BP.S5.S5_E09Statement)
    (hE10 : ThLean.BP.S5.S5_E10Statement) :
    ThLean.BP.S5.S5_35Statement := by
  intro q hq
  have hmean : 0 < ThresholdFoundations.lowMeanBound q := by
    unfold ThresholdFoundations.lowMeanBound
    have hqreal : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
    have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
    have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hqreal
    positivity
  have hA : 0 < Real.exp 1 * ThresholdFoundations.lowMeanBound q := by positivity

  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    hE09.2.2.2
  have hevLogLog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (Real.log n) :=
    hloglog.eventually_gt_atTop 0

  have hratio := hE10 (Real.exp 1 * ThresholdFoundations.lowMeanBound q) hA
  have hevRatio : ∀ᶠ n : ℕ in atTop,
      (if n < 16 then 0 else
        Real.log (Real.exp 1 * ThresholdFoundations.lowMeanBound q *
          Real.log (Real.log n)) / Real.log (Real.log n)) < (1 / 8 : ℝ) :=
    hratio.eventually (Iio_mem_nhds (by norm_num))
  have hevCond : ∀ᶠ n : ℕ in atTop,
      Real.log (Real.exp 1 * ThresholdFoundations.lowMeanBound q *
        Real.log (Real.log n)) ≤ (1 / 8 : ℝ) * Real.log (Real.log n) := by
    filter_upwards [hevRatio, hevLogLog, eventually_ge_atTop (16 : ℕ)] with n hr hu hn
    have hr' : Real.log (Real.exp 1 * ThresholdFoundations.lowMeanBound q *
        Real.log (Real.log n)) / Real.log (Real.log n) < (1 / 8 : ℝ) := by
      simpa [show ¬ n < 16 by omega] using hr
    exact le_of_lt ( (div_lt_iff₀ hu).mp hr')

  have hlogPow₁ : Tendsto
      (fun n : ℕ => if n < 3 then 0 else
        (Real.log n)^(1 / 4 : ℝ) / (n : ℝ)^(1 / 8 : ℝ)) atTop (nhds 0) :=
    hE09.1 (1 / 8 : ℝ) (1 / 4 : ℝ) (by norm_num)
  have hlogPow₂ : Tendsto
      (fun n : ℕ => if n < 3 then 0 else
        (Real.log n)^(1 / 2 : ℝ) / (n : ℝ)^(3 / 8 : ℝ)) atTop (nhds 0) :=
    hE09.1 (3 / 8 : ℝ) (1 / 2 : ℝ) (by norm_num)
  have hnegPow : Tendsto (fun n : ℕ => (n : ℝ)^(-(3 / 8 : ℝ))) atTop (nhds 0) :=
    hE09.2.1 (3 / 8 : ℝ) (by norm_num)
  have hevSmall₁ : ∀ᶠ n : ℕ in atTop,
      (if n < 3 then 0 else
        (Real.log n)^(1 / 4 : ℝ) / (n : ℝ)^(1 / 8 : ℝ)) < (1 / 3 : ℝ) :=
    hlogPow₁.eventually (Iio_mem_nhds (by norm_num))
  have hevSmall₂ : ∀ᶠ n : ℕ in atTop,
      (if n < 3 then 0 else
        (Real.log n)^(1 / 2 : ℝ) / (n : ℝ)^(3 / 8 : ℝ)) < (1 / 3 : ℝ) :=
    hlogPow₂.eventually (Iio_mem_nhds (by norm_num))
  have hevSmall₃ : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)^(-(3 / 8 : ℝ)) < (1 / 3 : ℝ) :=
    hnegPow.eventually (Iio_mem_nhds (by norm_num))

  have hevPoly : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)^(1 / 4 : ℝ) * (Real.log n)^(1 / 4 : ℝ) +
        (Real.log n)^(1 / 2 : ℝ) + 1 ≤ (n : ℝ)^(3 / 8 : ℝ) := by
    filter_upwards [hevSmall₁, hevSmall₂, hevSmall₃,
      eventually_ge_atTop (16 : ℕ)] with n h₁ h₂ h₃ hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hden : (n : ℝ)^(3 / 8 : ℝ) =
        (n : ℝ)^(1 / 4 : ℝ) * (n : ℝ)^(1 / 8 : ℝ) := by
      rw [show (3 / 8 : ℝ) = (1 / 4 : ℝ) + (1 / 8 : ℝ) by norm_num,
        Real.rpow_add hnreal]
    have h₁' : (Real.log (n : ℝ))^(1 / 4 : ℝ) /
        (n : ℝ)^(1 / 8 : ℝ) < (1 / 3 : ℝ) := by
      simpa [show ¬ n < 3 by omega] using h₁
    have h₂' : (Real.log (n : ℝ))^(1 / 2 : ℝ) /
        (n : ℝ)^(3 / 8 : ℝ) < (1 / 3 : ℝ) := by
      simpa [show ¬ n < 3 by omega] using h₂
    have h₁eq :
        ((n : ℝ)^(1 / 4 : ℝ) * (Real.log (n : ℝ))^(1 / 4 : ℝ)) /
            (n : ℝ)^(3 / 8 : ℝ) =
          (Real.log (n : ℝ))^(1 / 4 : ℝ) / (n : ℝ)^(1 / 8 : ℝ) := by
      rw [hden]
      have hp : 0 < (n : ℝ)^(1 / 4 : ℝ) := Real.rpow_pos_of_pos hnreal _
      field_simp
    have h₃eq : 1 / (n : ℝ)^(3 / 8 : ℝ) = (n : ℝ)^(-(3 / 8 : ℝ)) := by
      simpa [one_div] using
        (Real.rpow_neg (le_of_lt hnreal) (3 / 8 : ℝ)).symm
    have htotal :
        ((n : ℝ)^(1 / 4 : ℝ) * (Real.log n)^(1 / 4 : ℝ) +
          (Real.log n)^(1 / 2 : ℝ) + 1) / (n : ℝ)^(3 / 8 : ℝ) ≤ 1 := by
      calc
        _ = ((n : ℝ)^(1 / 4 : ℝ) * (Real.log n)^(1 / 4 : ℝ)) /
              (n : ℝ)^(3 / 8 : ℝ) +
            (Real.log n)^(1 / 2 : ℝ) / (n : ℝ)^(3 / 8 : ℝ) +
            1 / (n : ℝ)^(3 / 8 : ℝ) := by ring
        _ = (Real.log (n : ℝ))^(1 / 4 : ℝ) / (n : ℝ)^(1 / 8 : ℝ) +
            (Real.log (n : ℝ))^(1 / 2 : ℝ) / (n : ℝ)^(3 / 8 : ℝ) +
            (n : ℝ)^(-(3 / 8 : ℝ)) := by rw [h₁eq, h₃eq]
        _ ≤ 1 := by linarith
    have hpos : 0 < (n : ℝ)^(3 / 8 : ℝ) := Real.rpow_pos_of_pos hnreal _
    have hmul := (div_le_iff₀ hpos).mp htotal
    nlinarith

  have hevOnset : ∀ᶠ n : ℕ in atTop,
      ThresholdFoundations.lowSizeOnset q ≤ n - 1 := by
    filter_upwards [eventually_ge_atTop (ThresholdFoundations.lowSizeOnset q + 1)]
      with n hn
    omega
  have hevN : ∀ᶠ n : ℕ in atTop, 16 ≤ n :=
    eventually_ge_atTop 16
  have hevGood : ∀ᶠ n : ℕ in atTop, ThLean.BP.S5.GoodSize q n := by
    filter_upwards [hevN, hevOnset, hevLogLog, hevCond, hevPoly]
      with n hn₁ hn₂ hn₃ hn₄ hn₅
    exact ⟨hn₁, hn₂, hn₃, hn₄, hn₅⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hevGood
  exact ⟨n₀, fun n hn => hn₀ n hn⟩

example (hE09 : ThLean.BP.S5.S5_E09Statement)
    (hE10 : ThLean.BP.S5.S5_E10Statement) :
    ThLean.BP.S5.S5_35Statement :=
  S5_35Statement_of_deps hE09 hE10

end ThLean.W.S532

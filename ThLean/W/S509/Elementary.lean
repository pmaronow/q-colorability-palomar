import ThLean.BP.S5.Elementary
import Mathlib.Analysis.SpecialFunctions.Stirling

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S509
open ThLean.BP.S5 ThresholdFoundations

private theorem factorialMoment (μ : ℝ) (k : ℕ) :
    HasSum (fun j : ℕ => (j.choose k : ℝ) * poissonWeight μ j)
      (μ ^ k / (k.factorial : ℝ)) := by
  let f : ℕ → ℝ := fun j => (j.choose k : ℝ) * poissonWeight μ j
  have hexp : HasSum (fun j : ℕ => μ ^ j / (j.factorial : ℝ)) (Real.exp μ) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp μ
  have hshift : HasSum (fun j : ℕ => f (j + k))
      (Real.exp (-μ) * μ ^ k / (k.factorial : ℝ) * Real.exp μ) := by
    have hterm (j : ℕ) : f (j + k) =
        (Real.exp (-μ) * μ ^ k / (k.factorial : ℝ)) *
          (μ ^ j / (j.factorial : ℝ)) := by
      have hfacN := Nat.add_choose_mul_factorial_mul_factorial j k
      have hfac : ((j + k).choose k : ℝ) * (k.factorial : ℝ) * (j.factorial : ℝ) =
          ((j + k).factorial : ℝ) := by
        have hfac' : ((j + k).choose k : ℝ) * (j.factorial : ℝ) * (k.factorial : ℝ) =
            ((j + k).factorial : ℝ) := by exact_mod_cast hfacN
        nlinarith [hfac']
      unfold f poissonWeight
      have hfact0 : (k.factorial : ℝ) ≠ 0 := by positivity
      have hfact1 : (j.factorial : ℝ) ≠ 0 := by positivity
      have hfact2 : ((j + k).factorial : ℝ) ≠ 0 := by positivity
      rw [pow_add]
      field_simp [hfact0, hfact1, hfact2]
      calc
        ((j + k).choose k : ℝ) * μ ^ j * μ ^ k * (k.factorial : ℝ) *
            (j.factorial : ℝ) =
            μ ^ j * μ ^ k *
              (((j + k).choose k : ℝ) * (k.factorial : ℝ) * (j.factorial : ℝ)) := by ring
        _ = μ ^ j * μ ^ k * ((j + k).factorial : ℝ) := by rw [hfac]
    have hbase := hexp.mul_left (Real.exp (-μ) * μ ^ k / (k.factorial : ℝ))
    exact hbase.congr_fun hterm
  have hprefix : ∑ j ∈ Finset.range k, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    simp [f, Nat.choose_eq_zero_of_lt hjk]
  have hfull : HasSum f (μ ^ k / (k.factorial : ℝ)) := by
    apply (hasSum_nat_add_iff' k).mp
    simpa [hprefix, f, Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hshift
  simpa [f] using hfull

theorem S5_E04Statement_holds : ThLean.BP.S5.S5_E04Statement := by
  intro μ hμ
  refine ⟨?_, ?_⟩
  · intro k
    exact factorialMoment μ k
  · intro k hk
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
    have hfac' : ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
      have hrad : 1 ≤ 2 * Real.pi * (k : ℝ) := by
        have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
        have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
        calc
          1 ≤ 2 * Real.pi := hpi
          _ = 2 * Real.pi * 1 := by ring
          _ ≤ 2 * Real.pi * (k : ℝ) :=
            mul_le_mul_of_nonneg_left hk1 (by positivity)
      have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := Real.one_le_sqrt.mpr hrad
      have hbasepos : 0 < ((k : ℝ) / Real.exp 1) ^ k :=
        pow_pos (div_pos hkpos (Real.exp_pos 1)) _
      calc
        ((k : ℝ) / Real.exp 1) ^ k = 1 * ((k : ℝ) / Real.exp 1) ^ k := by ring
        _ ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k :=
          mul_le_mul_of_nonneg_right hsqrt (le_of_lt hbasepos)
        _ ≤ (k.factorial : ℝ) := Stirling.le_factorial_stirling k
    have hfacpos : 0 < (k.factorial : ℝ) := by positivity
    have hbasepos : 0 < ((k : ℝ) / Real.exp 1) ^ k := by
      exact pow_pos (div_pos hkpos (Real.exp_pos 1)) _
    have hrecip : 1 / (k.factorial : ℝ) ≤ 1 / ((k : ℝ) / Real.exp 1) ^ k :=
      one_div_le_one_div_of_le hbasepos hfac'
    have hpow : 0 ≤ μ ^ k := pow_nonneg hμ k
    have hfirst : μ ^ k / (k.factorial : ℝ) ≤ (Real.exp 1 * μ / k) ^ k := by
      calc
        μ ^ k / (k.factorial : ℝ) = μ ^ k * (1 / (k.factorial : ℝ)) := by ring
        _ ≤ μ ^ k * (1 / ((k : ℝ) / Real.exp 1) ^ k) := mul_le_mul_of_nonneg_left hrecip hpow
        _ = (Real.exp 1 * μ / k) ^ k := by
          rw [one_div, div_pow, inv_div, div_pow, mul_pow]
          ring
    have hmom := factorialMoment μ k
    have hw (j : ℕ) : 0 ≤ poissonWeight μ j := by
      unfold poissonWeight
      exact div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hμ _)) (Nat.cast_nonneg _)
    have hmomentNonneg : ∀ j, 0 ≤ (j.choose k : ℝ) * poissonWeight μ j := by
      intro j
      exact mul_nonneg (Nat.cast_nonneg _) (hw j)
    have hchoose : ∀ j, (if k ≤ j then poissonWeight μ j else 0) ≤
        (j.choose k : ℝ) * poissonWeight μ j := by
      intro j
      by_cases hj : k ≤ j
      · have hc : (1 : ℝ) ≤ (j.choose k : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos hj))
        simpa [hj] using mul_le_mul_of_nonneg_right hc (hw j)
      · simp [hj, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)]
    have hstrict : ∀ j, (if k < j then poissonWeight μ j else 0) ≤
        (j.choose k : ℝ) * poissonWeight μ j := by
      intro j
      by_cases hj : k < j
      · have hc : (1 : ℝ) ≤ (j.choose k : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos hj.le))
        simpa [hj] using mul_le_mul_of_nonneg_right hc (hw j)
      · simp [hj]
        exact hmomentNonneg j
    have htail1Nonneg : ∀ j, 0 ≤ (if k ≤ j then poissonWeight μ j else 0) := by
      intro j
      by_cases hj : k ≤ j <;> simp [hj, hw]
    have htail2Nonneg : ∀ j, 0 ≤ (if k < j then poissonWeight μ j else 0) := by
      intro j
      by_cases hj : k < j <;> simp [hj, hw]
    have htail₁ : Summable (fun j : ℕ => if k ≤ j then poissonWeight μ j else 0) :=
      hmom.summable.of_nonneg_of_le htail1Nonneg hchoose
    have htail₂ : Summable (fun j : ℕ => if k < j then poissonWeight μ j else 0) :=
      hmom.summable.of_nonneg_of_le htail2Nonneg hstrict
    have hsum₁ := htail₁.tsum_le_tsum hchoose hmom.summable
    have hsum₂ := htail₂.tsum_le_tsum hstrict hmom.summable
    refine ⟨?_, hfirst, ?_⟩
    · exact hsum₁.trans_eq hmom.tsum_eq
    · calc
        (∑' j : ℕ, if k < j then poissonWeight μ j else 0) ≤
            ∑' j : ℕ, (j.choose k : ℝ) * poissonWeight μ j := hsum₂
        _ = μ ^ k / (k.factorial : ℝ) := hmom.tsum_eq
        _ ≤ (Real.exp 1 * μ / k) ^ k := hfirst

end ThLean.W.S509

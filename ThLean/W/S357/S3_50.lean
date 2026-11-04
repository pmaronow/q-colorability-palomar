module

public import ThLean.BP.S3.Tails
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators
namespace ThLean.W.S357
open ThresholdFoundations ThLean.BP.S3

private lemma poissonWeight_shift_le (z : ℝ) (m j : ℕ) (hz : 0 ≤ z)
    (hfac : ∀ a b : ℕ, a.factorial * b.factorial ≤ (a+b).factorial) :
    poissonWeight z (m+j) ≤ poissonWeight z m * z^j / (j.factorial : ℝ) := by
  have hfac' : (m.factorial : ℝ) * (j.factorial : ℝ) ≤ ((m+j).factorial : ℝ) := by
    exact_mod_cast hfac m j
  have hm : 0 < (m.factorial : ℝ) := by positivity
  have hj : 0 < (j.factorial : ℝ) := by positivity
  have hmj : 0 < ((m+j).factorial : ℝ) := by positivity
  have hnum : 0 ≤ Real.exp (-z) * (z^m * z^j) := by positivity
  unfold poissonWeight
  rw [pow_add]
  calc
    Real.exp (-z) * (z^m * z^j) / ((m+j).factorial : ℝ) ≤
        Real.exp (-z) * (z^m * z^j) / ((m.factorial : ℝ) * (j.factorial : ℝ)) :=
      div_le_div_of_nonneg_left hnum (mul_pos hm hj) hfac'
    _ = (Real.exp (-z) * z^m / (m.factorial : ℝ)) * z^j / (j.factorial : ℝ) := by
      field_simp

private lemma poissonTail_eq_tsum_shift (z : ℝ) (i : ℕ) (hz : 0 ≤ z)
    (h31 : S3_31Statement) :
    poissonTail z (i : ℝ) = ∑' j : ℕ, poissonWeight z (i+j) := by
  let f : ℕ → ℝ := fun n => poissonWeight z n
  let g : ℕ → ℝ := fun n => if i ≤ n then f n else 0
  have hf_nonneg : ∀ n, 0 ≤ f n := (h31 z hz).1
  have hf_sum : Summable f := (h31 z hz).2.1
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    simp only [g]
    split_ifs <;> simp [hf_nonneg]
  have hg_le : ∀ n, g n ≤ f n := by
    intro n
    simp only [g]
    split_ifs with h
    · exact le_rfl
    · exact (hf_nonneg n)
  have hg_sum : Summable g := Summable.of_nonneg_of_le hg_nonneg hg_le hf_sum
  have hshift_sum : Summable (fun n : ℕ => g (n+i)) :=
    (summable_nat_add_iff (f := g) i).2 hg_sum
  have hsplit := hshift_sum.sum_add_tsum_nat_add'
  have hprefix : (∑ n ∈ Finset.range i, g n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [g, hn]
  have hshift : (∑' n : ℕ, g n) = ∑' j : ℕ, f (i+j) := by
    have hpoint : ∀ n, g (n+i) = f (n+i) := by
      intro n
      have hi' : i ≤ n+i := by omega
      simp [g, hi']
    have hsplit' := hsplit
    rw [hprefix, zero_add] at hsplit'
    rw [tsum_congr hpoint] at hsplit'
    simpa [Nat.add_comm] using hsplit'.symm
  have hENN : poissonTailENN z (i : ℝ) = ENNReal.ofReal (∑' n : ℕ, g n) := by
    rw [poissonTailENN]
    calc
      (∑' k : ℕ, if (i : ℝ) ≤ (k : ℝ) then ENNReal.ofReal (poissonWeight z k) else 0) =
          ∑' n : ℕ, ENNReal.ofReal (g n) := by
        apply tsum_congr
        intro n
        by_cases hn : i ≤ n
        · simp [g, f, hn]
        · have hn' : ¬ (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          simp [g, f, hn, hn']
      _ = ENNReal.ofReal (∑' n : ℕ, g n) :=
        (ENNReal.ofReal_tsum_of_nonneg hg_nonneg hg_sum).symm
  have htsum_nonneg : 0 ≤ ∑' j : ℕ, poissonWeight z (i+j) := by
    apply tsum_nonneg
    intro j
    exact hf_nonneg (i+j)
  rw [poissonTail, hENN, hshift, ENNReal.toReal_ofReal htsum_nonneg]

theorem S3_50Statement_of_deps (h31 : S3_31Statement) (h42 : S3_42Statement) :
    S3_50Statement := by
  intro z i hz hi
  have hfac := h42.2.2
  have hweight_sum : Summable (poissonWeight z) := (h31 z hz).2.1
  have hpow_sum : Summable (fun j : ℕ => z^j / (j.factorial : ℝ)) := by
    simpa using Real.summable_pow_div_factorial z
  have hpow_shift : Summable (fun j : ℕ => z^(j+1) / ((j+1).factorial : ℝ)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff (f := fun n : ℕ => z^n / (n.factorial : ℝ)) 1).2 hpow_sum
  have hseries_shift : (∑' j : ℕ, z^(j+1) / ((j+1).factorial : ℝ)) = Real.exp z - 1 := by
    have hsplit := Summable.sum_add_tsum_nat_add'
      (f := fun n : ℕ => z^n / (n.factorial : ℝ)) (k := 1) hpow_shift
    have hexp : (∑' n : ℕ, z^n / (n.factorial : ℝ)) = Real.exp z := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hexp] at hsplit
    have hpref : (∑ n ∈ Finset.range 1, z^n / (n.factorial : ℝ)) = 1 := by simp
    rw [hpref] at hsplit
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hsplit
  have htail := poissonTail_eq_tsum_shift z i hz h31
  have hterm : ∀ j : ℕ,
      poissonWeight z (i+j) ≤
        poissonWeight z (i-1) * z^(j+1) / ((j+1).factorial : ℝ) := by
    intro j
    have hrepr : i+j = (i-1)+(j+1) := by omega
    rw [hrepr]
    exact poissonWeight_shift_le z (i-1) (j+1) hz hfac
  have hmajor_summable : Summable (fun j : ℕ =>
      poissonWeight z (i-1) * z^(j+1) / ((j+1).factorial : ℝ)) := by
    have hmul := hpow_shift.mul_left (poissonWeight z (i-1))
    convert hmul using 1 <;> ext j <;> ring
  have hshift_weight : Summable (fun j : ℕ => poissonWeight z (i+j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff (f := poissonWeight z) i).2 hweight_sum
  have htail_le : poissonTail z (i : ℝ) ≤
      (Real.exp z - 1) * poissonWeight z (i-1) := by
    rw [htail]
    calc
      (∑' j : ℕ, poissonWeight z (i+j)) ≤
          ∑' j : ℕ, poissonWeight z (i-1) * z^(j+1) / ((j+1).factorial : ℝ) :=
        hshift_weight.tsum_le_tsum hterm hmajor_summable
      _ = poissonWeight z (i-1) * (Real.exp z - 1) := by
        calc
          _ = ∑' j : ℕ, poissonWeight z (i-1) *
              (z^(j+1) / ((j+1).factorial : ℝ)) := by
            apply tsum_congr
            intro j
            ring
          _ = poissonWeight z (i-1) *
              (∑' j : ℕ, z^(j+1) / ((j+1).factorial : ℝ)) :=
            hpow_shift.tsum_mul_left (poissonWeight z (i-1))
          _ = poissonWeight z (i-1) * (Real.exp z - 1) := by rw [hseries_shift]
      _ = (Real.exp z - 1) * poissonWeight z (i-1) := by ring
  refine ⟨htail_le, ?_, ?_, ?_⟩
  · intro j hj
    have hrepr : i-1+j = (i-1)+j := rfl
    exact poissonWeight_shift_le z (i-1) j hz hfac
  · exact hshift_weight
  · have hmul := hpow_shift.mul_left (poissonWeight z (i-1))
    convert hmul using 1 <;> ext j <;> ring

end ThLean.W.S357

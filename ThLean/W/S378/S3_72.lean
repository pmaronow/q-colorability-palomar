import ThLean.BP.S3.Centre

noncomputable section
open scoped BigOperators

namespace ThLean.W.S378

open ThLean.BP.S3

private theorem obstructionSeries_formula (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun j : ℕ => ((j+4 : ℕ) : ℝ)^2 * a^(j+3)) ∧
      obstructionSeries a = a^3*(16-23*a+9*a^2)/(1-a)^3 := by
  have hnorm : ‖a‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ha0]
    exact ha1
  have h0 : Summable (fun j : ℕ => a ^ j) := summable_geometric_of_lt_one ha0 ha1
  have h1 : Summable (fun j : ℕ => (j : ℝ) * a ^ j) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h2 : Summable (fun j : ℕ => (j : ℝ)^2 * a ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have hsum : Summable (fun j : ℕ => a^3 *
      ((j : ℝ)^2 * a^j + (8*((j : ℝ)*a^j) + 16*a^j))) := by
    have h := h2.add ((h1.mul_left 8).add (h0.mul_left 16))
    exact h.mul_left (a^3)
  have hterm (j : ℕ) : ((j+4 : ℕ) : ℝ)^2 * a^(j+3) =
      a^3 * ((j : ℝ)^2 * a^j + (8*((j : ℝ)*a^j) + 16*a^j)) := by
    rw [pow_add]
    push_cast
    ring
  refine ⟨hsum.congr (fun j => (hterm j).symm), ?_⟩
  have hA : tsum (fun j : ℕ => (j : ℝ)^2 * a^j) = a*(1+a)/(1-a)^3 :=
    tsum_sq_mul_geometric_of_norm_lt_one hnorm
  have hB : tsum (fun j : ℕ => (j : ℝ) * a^j) = a/(1-a)^2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hC : tsum (fun j : ℕ => a^j) = (1-a)⁻¹ :=
    tsum_geometric_of_lt_one ha0 ha1
  have hneq : 1-a ≠ 0 := by linarith
  unfold obstructionSeries
  calc
    (∑' j : ℕ, ((j+4 : ℕ) : ℝ)^2 * a^(j+3)) =
        ∑' j : ℕ, a^3 * ((j : ℝ)^2 * a^j + (8*((j : ℝ)*a^j) + 16*a^j)) :=
      tsum_congr hterm
    _ = a^3 * ∑' j : ℕ, ((j : ℝ)^2 * a^j + (8*((j : ℝ)*a^j) + 16*a^j)) := by
      rw [tsum_mul_left]
    _ = a^3 * ((∑' j : ℕ, (j : ℝ)^2 * a^j) +
        (8*(∑' j : ℕ, (j : ℝ)*a^j) + 16*(∑' j : ℕ, a^j))) := by
      rw [h2.tsum_add ((h1.mul_left 8).add (h0.mul_left 16)),
        (h1.mul_left 8).tsum_add (h0.mul_left 16), tsum_mul_left, tsum_mul_left]
    _ = a^3*(16-23*a+9*a^2)/(1-a)^3 := by
      rw [hA, hB, hC]
      field_simp [hneq]
      ring

theorem S3_72Statement_holds : ThLean.BP.S3.S3_72Statement := by
  constructor
  · intro a ha0 ha1
    exact obstructionSeries_formula a ha0 ha1
  · have h := (obstructionSeries_formula (1/2) (by norm_num) (by norm_num)).2
    rw [h]
    norm_num

end ThLean.W.S378

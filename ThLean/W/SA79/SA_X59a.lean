import ThLean.BP.SA.Transfer

noncomputable section
open Filter

namespace ThLean.W.SA79

theorem SA_X59aStatement_holds : ThLean.BP.SA.SA_X59aStatement := by
  intro c hc
  let N : ℕ := Nat.ceil (2 * c + 1)
  have hceil : 2 * c + 1 ≤ (N : ℝ) := by
    exact Nat.le_ceil _
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
  constructor
  · have hnreal : 2 * c + 1 ≤ (n : ℝ) := by
      exact le_trans hceil (by exact_mod_cast hn)
    have hnpos : 1 ≤ (n : ℝ) := by linarith
    have hcoeff : 2 * c ≤ (n : ℝ) - 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)
    have hchoose : c * (n : ℝ) ≤ (n.choose 2 : ℝ) := by
      rw [Nat.cast_choose_two]
      nlinarith
    have hfloor : (Nat.floor (c * n : ℝ) : ℝ) ≤ c * n :=
      Nat.floor_le (mul_nonneg hc (Nat.cast_nonneg n))
    exact_mod_cast hfloor.trans hchoose
  · exact Int.natCast_floor_eq_floor (mul_nonneg hc (Nat.cast_nonneg n))

end ThLean.W.SA79

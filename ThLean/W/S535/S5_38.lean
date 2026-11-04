module

public import ThLean.BP.S5.Main

@[expose] public section

noncomputable section
open Real

namespace ThLean.W.S535

open ThresholdFoundations

/-- The logarithmic tail estimate at the low-degree truncation. -/
theorem S5_38Statement_holds : ThLean.BP.S5.S5_38Statement := by
  intro q n hq hn hsize hcond
  let x : ℝ := Real.log (n : ℝ)
  let L : ℝ := Real.log x
  let d : ℝ := (degreeCut n : ℝ)
  let k : ℝ := (lowTruncation n : ℝ)
  let z : ℝ := lowMeanBound q
  let R : ℝ := Real.exp 1 * d * z / k

  have hnpos : 0 < (n : ℝ) := by positivity
  have h3n : (3 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 3 ≤ n by omega)
  have hexp : Real.exp 1 < (n : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three h3n
  have hxgt1 : 1 < x := by
    change 1 < Real.log (n : ℝ)
    exact (Real.lt_log_iff_exp_lt hnpos).2 hexp
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by
    change 0 < Real.log x
    exact Real.log_pos hxgt1
  have hdNat : 1 ≤ degreeCut n := by
    rw [degreeCut, Nat.one_le_floor_iff]
    exact Real.one_le_rpow (le_of_lt hxgt1) (by norm_num)
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast (show 0 < degreeCut n by omega)
  have hdle : d ≤ x ^ (1 / 4 : ℝ) := by
    dsimp [d, x]
    unfold degreeCut
    exact Nat.floor_le
      (Real.rpow_pos_of_pos (by simpa [x] using hxpos) _).le
  have hratioPos : 0 < x / L := div_pos hxpos hLpos
  have hklo : x / L ≤ k := by
    dsimp [x, L, k]
    unfold lowTruncation
    exact Nat.le_ceil _
  have hkpos : 0 < k := lt_of_lt_of_le hratioPos hklo
  have hqgt1 : 1 < (q : ℝ) := by
    exact_mod_cast (show 1 < q by omega)
  have hzpos : 0 < z := by
    dsimp [z, lowMeanBound]
    have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqgt1
    positivity
  have hRpos : 0 < R := by
    dsimp [R]
    positivity

  have hlogd : Real.log d ≤ (1 / 4 : ℝ) * L := by
    calc
      Real.log d ≤ Real.log (x ^ (1 / 4 : ℝ)) :=
        Real.log_le_log hdpos hdle
      _ = (1 / 4 : ℝ) * L := by
        rw [Real.log_rpow hxpos]
  have hlogk : Real.log (x / L) ≤ Real.log k :=
    Real.log_le_log hratioPos hklo
  have hlogratio : Real.log (x / L) = L - Real.log L := by
    rw [Real.log_div hxpos.ne' hLpos.ne']
  have hlogR : Real.log R = 1 + Real.log d + Real.log z - Real.log k := by
    change Real.log (Real.exp 1 * d * z / k) = _
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hcond' : Real.log (Real.exp 1 * z * L) ≤ (1 / 8 : ℝ) * L := by
    simpa [x, z] using hcond
  have hlogProduct :
      1 + Real.log z + Real.log L = Real.log (Real.exp 1 * z * L) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp]
  have hlogRle : Real.log R ≤ -(5 / 8 : ℝ) * L := by
    calc
      Real.log R = 1 + Real.log d + Real.log z - Real.log k := hlogR
      _ ≤ 1 + (1 / 4 : ℝ) * L + Real.log z - Real.log (x / L) := by
        linarith [hlogd, hlogk]
      _ = Real.log (Real.exp 1 * z * L) - (3 / 4 : ℝ) * L := by
        rw [hlogratio, ← hlogProduct]
        ring
      _ ≤ -(5 / 8 : ℝ) * L := by
        linarith [hcond']
  have hRle : R ≤ Real.exp (-(5 / 8 : ℝ) * L) := by
    rw [← Real.exp_log hRpos]
    exact Real.exp_le_exp.mpr hlogRle
  have hExpLtOne : Real.exp (-(5 / 8 : ℝ) * L) < 1 := by
    apply Real.exp_lt_one_iff.2
    nlinarith [hLpos]
  have hRltOne : R < 1 := lt_of_le_of_lt hRle hExpLtOne
  have hstrict : Real.exp 1 * d * z < k := by
    have hmul := (div_lt_iff₀ hkpos).1 (by simpa [R] using hRltOne)
    simpa using hmul

  have harg : (-(5 / 8 : ℝ)) * L * k ≤ (-(5 / 8 : ℝ)) * x := by
    have hxle : x ≤ L * k := by
      have := (div_le_iff₀ hLpos).1 hklo
      nlinarith
    have hmul := mul_le_mul_of_nonpos_left hxle (by norm_num : (-(5 / 8 : ℝ)) ≤ 0)
    nlinarith
  have hpowR : R ^ lowTruncation n ≤ Real.exp (-(5 / 8 : ℝ) * x) := by
    calc
      R ^ lowTruncation n ≤ Real.exp (-(5 / 8 : ℝ) * L) ^ lowTruncation n :=
        pow_le_pow_left₀ hRpos.le hRle _
      _ = Real.exp ((lowTruncation n : ℝ) * ((-(5 / 8 : ℝ)) * L)) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (-(5 / 8 : ℝ) * x) := by
        apply Real.exp_le_exp.mpr
        dsimp [k] at harg ⊢
        nlinarith
  have hnm1 : 0 ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  have hnm1le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.sub_le n 1)
  have hnfinal : (n : ℝ) * Real.exp (-(5 / 8 : ℝ) * x) =
      (n : ℝ) ^ (3 / 8 : ℝ) := by
    calc
      (n : ℝ) * Real.exp (-(5 / 8 : ℝ) * x) =
          Real.exp (Real.log (n : ℝ)) * Real.exp (-(5 / 8 : ℝ) * x) := by
            rw [Real.exp_log hnpos]
      _ = Real.exp (Real.log (n : ℝ) + (-(5 / 8 : ℝ) * x)) := by
        rw [← Real.exp_add]
      _ = Real.exp (Real.log (n : ℝ) * (3 / 8 : ℝ)) := by
        congr 1
        dsimp [x]
        ring
      _ = (n : ℝ) ^ (3 / 8 : ℝ) := (Real.rpow_def_of_pos hnpos _).symm

  refine ⟨hRpos, hRle, hExpLtOne, ?_, ?_⟩
  · simpa [d, z, k] using hstrict
  · calc
      ((n - 1 : ℕ) : ℝ) * R ^ lowTruncation n ≤
          ((n - 1 : ℕ) : ℝ) * Real.exp (-(5 / 8 : ℝ) * x) :=
        mul_le_mul_of_nonneg_left hpowR hnm1
      _ ≤ (n : ℝ) * Real.exp (-(5 / 8 : ℝ) * x) :=
        mul_le_mul_of_nonneg_right hnm1le (Real.exp_pos _).le
      _ = (n : ℝ) ^ (3 / 8 : ℝ) := hnfinal

example : ThLean.BP.S5.S5_38Statement := S5_38Statement_holds

end ThLean.W.S535

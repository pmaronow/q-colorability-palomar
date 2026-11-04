module

public import ThLean.BP.S3.Lifetime

@[expose] public section

namespace ThLean.W.S331

theorem S3_30aStatement_holds : ThLean.BP.S3.S3_30aStatement := by
  intro N A κ Q r hN hA hκ hr hAr hκr hQ
  have hNpos : 0 < N := by linarith
  have hNge1 : (1 : ℝ) ≤ N := by linarith
  have hInv : 1 / N ≤ 1 := by
    calc
      1 / N ≤ 1 / 1 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hNge1
      _ = 1 := by norm_num
  have hcoeff_nonneg : 0 ≤ 1 - 1 / N := by linarith
  have hcoeff_le_one : 1 - 1 / N ≤ 1 := by
    have hInv_nonneg : 0 ≤ 1 / N := by positivity
    linarith
  have hrN : r / N ≤ A := (div_le_iff₀ hNpos).2 hAr
  have hprod : (1 - 1 / N) * (κ * r) ≤ 1 := by
    calc
      (1 - 1 / N) * (κ * r) ≤ (1 - 1 / N) * 1 :=
        mul_le_mul_of_nonneg_left hκr hcoeff_nonneg
      _ ≤ 1 := by simpa using hcoeff_le_one
  have hQmul : Q * r = (1 - 1 / N) * (κ * r) + r / N := by
    rw [hQ]
    ring
  have hmain : Q * r ≤ 1 + A := by
    rw [hQmul]
    linarith
  have hrpos : 0 < r := by linarith
  have h1A : 0 < 1 + A := by linarith
  refine ⟨hmain, ?_⟩
  intro y hy hyr
  have hdiv : Q ≤ (1 + A) / r := (le_div_iff₀ hrpos).2 hmain
  have hstrictmul : (1 + A) * y < (1 + A) * r :=
    mul_lt_mul_of_pos_left hyr h1A
  have hstrict : (1 + A) / r < (1 + A) / y :=
    (div_lt_div_iff₀ hrpos hy).2 hstrictmul
  refine ⟨hdiv, hstrict, ?_⟩
  exact Real.sqrt_le_sqrt (le_trans hdiv hstrict.le)

end ThLean.W.S331

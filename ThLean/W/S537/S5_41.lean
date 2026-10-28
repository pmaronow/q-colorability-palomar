import ThLean.BP.S5.Main

noncomputable section
open Filter
open scoped Topology

namespace ThLean.W.S537

open ThLean.BP.S5
open ThresholdFoundations

theorem S5_41Statement_of_deps (hE09 : ThLean.BP.S5.S5_E09Statement) :
    ThLean.BP.S5.S5_41Statement := by
  intro C hC
  have hlim := hE09.1 (1 / 8 : ℝ) 3 (by norm_num)
  have hsmallEvent : ∀ᶠ n : ℕ in atTop,
      (if n < 3 then 0 else
        (Real.log (n : ℝ)) ^ (3 : ℝ) / (n : ℝ) ^ (1 / 8 : ℝ)) < 1 / C := by
    exact hlim.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmallEvent
  refine ⟨max N 3, by omega, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnlt : ¬ n < 3 := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hpow : 0 < (n : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hnR _
  have hratio : (Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ (1 / 8 : ℝ) < 1 / C := by
    simpa [hnlt, Real.rpow_natCast] using hN n hnN
  have hratio' : (Real.log (n : ℝ)) ^ 3 <
      (1 / C) * (n : ℝ) ^ (1 / 8 : ℝ) := (div_lt_iff₀ hpow).1 hratio
  have hstrict : C * (Real.log (n : ℝ)) ^ 3 < (n : ℝ) ^ (1 / 8 : ℝ) := by
    calc
      C * (Real.log (n : ℝ)) ^ 3 < C * ((1 / C) * (n : ℝ) ^ (1 / 8 : ℝ)) :=
        mul_lt_mul_of_pos_left hratio' hC
      _ = (n : ℝ) ^ (1 / 8 : ℝ) := by field_simp
  have hbound : C * (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ (1 / 8 : ℝ) := le_of_lt hstrict
  have heps : epsilon n = (Real.log (n : ℝ)) ^ (-(3 : ℝ) / 2) := by
    simp [epsilon, hnlt]
  have hepssq : ((Real.log (n : ℝ)) ^ (-(3 : ℝ) / 2)) ^ 2 =
      (Real.log (n : ℝ)) ^ (-3 : ℝ) := by
    calc
      ((Real.log (n : ℝ)) ^ (-(3 : ℝ) / 2)) ^ 2 =
          ((Real.log (n : ℝ)) ^ (-(3 : ℝ) / 2)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast _ _).symm
      _ = (Real.log (n : ℝ)) ^ ((-(3 : ℝ) / 2) * 2) := by
        rw [← Real.rpow_mul (le_of_lt hlog)]
      _ = (Real.log (n : ℝ)) ^ (-3 : ℝ) := by congr 1; norm_num
  have hcut : lifetimeCut n = (n : ℝ) * (Real.log (n : ℝ)) ^ (-3 : ℝ) := by
    unfold lifetimeCut
    rw [heps, hepssq]
  have hnegcut :
      ((n : ℝ) * (Real.log (n : ℝ)) ^ (-3 : ℝ)) ^ (-(1 / 2 : ℝ)) =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := by
    calc
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((Real.log (n : ℝ)) ^ (-3 : ℝ)) ^ (-(1 / 2 : ℝ) ) := by
        rw [Real.mul_rpow (le_of_lt hnR)
          (le_of_lt (Real.rpow_pos_of_pos hlog (-3 : ℝ)))]
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_mul (le_of_lt hlog) (-3 : ℝ) (-(1 / 2 : ℝ))]
        congr 1
        norm_num
  have hnexp : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (3 / 8 : ℝ) =
      (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
    calc
      _ = (n : ℝ) ^ ((-(1 / 2 : ℝ)) + (3 / 8 : ℝ)) :=
        (Real.rpow_add hnR _ _).symm
      _ = (n : ℝ) ^ (-(1 / 8 : ℝ)) := by congr 1; norm_num
  have hidentity :
      C * (lifetimeCut n) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (3 / 8 : ℝ) =
        C * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
    rw [hcut]
    calc
      C * ((n : ℝ) * (Real.log (n : ℝ)) ^ (-3 : ℝ)) ^ (-(1 / 2 : ℝ)) *
          (n : ℝ) ^ (3 / 8 : ℝ) =
        C * ((n : ℝ) ^ (-(1 / 2 : ℝ) ) *
          (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) * (n : ℝ) ^ (3 / 8 : ℝ) := by
            rw [hnegcut]
      _ = C * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (3 / 8 : ℝ)) := by ring
      _ = C * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
        rw [hnexp]
  have hepsInv : epsilon n = ((Real.log (n : ℝ)) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [heps]
    simpa only [show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) by norm_num] using
      (Real.rpow_neg (le_of_lt hlog) (3 / 2 : ℝ))
  have hlogpow : 0 < (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hlog _
  have hkey : C * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) *
      (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
    have hsquare : (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) *
        (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) = (Real.log (n : ℝ)) ^ 3 := by
      calc
        _ = (Real.log (n : ℝ)) ^ ((3 / 2 : ℝ) + (3 / 2 : ℝ)) :=
          (Real.rpow_add hlog _ _).symm
        _ = (Real.log (n : ℝ)) ^ (3 : ℝ) := by congr 1; norm_num
        _ = (Real.log (n : ℝ)) ^ 3 := Real.rpow_natCast _ _
    calc
      C * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) *
          (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) =
        C * ((Real.log (n : ℝ)) ^ (3 / 2 : ℝ) *
          (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) := by ring
      _ = C * (Real.log (n : ℝ)) ^ 3 := by rw [hsquare]
      _ ≤ (n : ℝ) ^ (1 / 8 : ℝ) := hbound
  have hdiv : C * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) ≤
      (n : ℝ) ^ (1 / 8 : ℝ) / (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) :=
    (le_div_iff₀ hlogpow).2 (by simpa [mul_assoc] using hkey)
  refine ⟨?_, hbound, hidentity, ?_⟩
  · rw [hcut]
    exact mul_pos hnR (Real.rpow_pos_of_pos hlog (-3 : ℝ))
  · rw [hidentity, hepsInv]
    rw [Real.rpow_neg (le_of_lt hnR) (1 / 8 : ℝ)]
    apply (div_le_iff₀ hpow).2
    calc
      C * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) ≤
          (n : ℝ) ^ (1 / 8 : ℝ) / (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := hdiv
      _ = ((Real.log (n : ℝ)) ^ (3 / 2 : ℝ))⁻¹ * (n : ℝ) ^ (1 / 8 : ℝ) := by
        rw [div_eq_mul_inv]
        ring

end ThLean.W.S537

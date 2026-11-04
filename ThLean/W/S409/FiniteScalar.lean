module

public import ThLean.BP.S4.Finite

@[expose] public section

noncomputable section

namespace ThLean.W.S409

open ThLean.BP.S4

theorem S4_ALG_02BStatement_holds : S4_ALG_02BStatement := by
  intro n ε Λ η K U w s t hn hε hΛ hη hK hU hw hUn hvar ht hconditional
  have hx : 0 < n * ε := mul_pos hn hε
  by_cases hsmall : w < n * ε
  · have hmax : (1 : ℝ) ≤ max 1 (2 * Λ * K / η ^ 2) := le_max_left _ _
    have hprod := mul_le_mul_of_nonneg_right hmax (le_of_lt hx)
    calc
      w ≤ n * ε := le_of_lt hsmall
      _ ≤ max 1 (2 * Λ * K / η ^ 2) * (n * ε) := by nlinarith
      _ = max 1 (2 * Λ * K / η ^ 2) * n * ε := by ring
  · have hwx : n * ε ≤ w := le_of_not_gt hsmall
    have hwpos : 0 < w := lt_of_lt_of_le hx hwx
    have hratio : 0 < w / (n * ε) := div_pos hwpos hx
    have hUpos : 0 < U := by
      by_contra hnot
      have hUzero : U = 0 := le_antisymm (le_of_not_gt hnot) hU
      rw [hUzero] at hvar
      have hleft : 0 < η ^ 2 * w ^ 2 := mul_pos (sq_pos_of_pos hη) (sq_pos_of_pos hwpos)
      nlinarith
    have hspos : 0 < s := by
      by_contra hnot
      have hsnonpos : s ≤ 0 := le_of_not_gt hnot
      have hprod : U * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hUpos) hsnonpos
      have hleft : 0 < η ^ 2 * w ^ 2 := mul_pos (sq_pos_of_pos hη) (sq_pos_of_pos hwpos)
      nlinarith [hleft]
    have htpos : 0 < t := by
      by_contra hnot
      have htnonpos : t ≤ 0 := le_of_not_gt hnot
      have hprod : (w / (n * ε)) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hratio) htnonpos
      have : s ≤ 0 := le_trans (hconditional hwx) hprod
      exact (not_lt_of_ge this) hspos
    have hscap : s ≤ (w / (n * ε)) * (K * n * ε ^ 2) :=
      le_trans (hconditional hwx) (mul_le_mul_of_nonneg_left ht (le_of_lt hratio))
    have hchain : η ^ 2 * w ^ 2 ≤ 2 * (Λ * n) * ((w / (n * ε)) * (K * n * ε ^ 2)) := by
      calc
        η ^ 2 * w ^ 2 ≤ 2 * U * s := hvar
        _ ≤ 2 * U * ((w / (n * ε)) * (K * n * ε ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hscap (by positivity)
        _ ≤ 2 * (Λ * n) * ((w / (n * ε)) * (K * n * ε ^ 2)) := by
          have hmul := mul_le_mul_of_nonneg_right hUn (by positivity : 0 ≤ 2 * ((w / (n * ε)) * (K * n * ε ^ 2)))
          nlinarith
    have hscaled : η ^ 2 * w ^ 2 ≤ 2 * Λ * K * w * (n * ε) := by
      calc
        η ^ 2 * w ^ 2 ≤ 2 * (Λ * n) * ((w / (n * ε)) * (K * n * ε ^ 2)) := hchain
        _ = 2 * Λ * K * w * (n * ε) := by field_simp [ne_of_gt hx]
    have hden : 0 < η ^ 2 * w := mul_pos (sq_pos_of_pos hη) hwpos
    have hcancel : w ≤ (2 * Λ * K * w * (n * ε)) / (η ^ 2 * w) := by
      apply (le_div_iff₀ hden).2
      nlinarith [hscaled]
    have hquot : (2 * Λ * K * w * (n * ε)) / (η ^ 2 * w) = (2 * Λ * K / η ^ 2) * (n * ε) := by
      field_simp [ne_of_gt hwpos, ne_of_gt hη]
    have hbound : w ≤ (2 * Λ * K / η ^ 2) * (n * ε) := hquot ▸ hcancel
    have hmax : 2 * Λ * K / η ^ 2 ≤ max 1 (2 * Λ * K / η ^ 2) := le_max_right _ _
    have hmaxprod := mul_le_mul_of_nonneg_right hmax (le_of_lt hx)
    calc
      w ≤ (2 * Λ * K / η ^ 2) * (n * ε) := hbound
      _ ≤ max 1 (2 * Λ * K / η ^ 2) * (n * ε) := hmaxprod
      _ = max 1 (2 * Λ * K / η ^ 2) * n * ε := by ring

end ThLean.W.S409

import ThLean.BP.S6.Analytic

namespace ThLean.W.S648

theorem S6_X01Statement_holds : ThLean.BP.S6.S6_X01Statement := by
  constructor
  · intro t k ht
    exact Real.pow_div_factorial_le_exp t ht k
  · intro t k ht
    have hterm : 0 < t ^ k / (k.factorial : ℝ) := by positivity
    have hbound : t ^ k / (k.factorial : ℝ) ≤ Real.exp t :=
      Real.pow_div_factorial_le_exp t ht.le k
    have hrecip : 1 / Real.exp t ≤ 1 / (t ^ k / (k.factorial : ℝ)) :=
      one_div_le_one_div_of_le hterm hbound
    calc
      Real.exp (-t) = 1 / Real.exp t := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / (t ^ k / (k.factorial : ℝ)) := hrecip
      _ = (k.factorial : ℝ) / t ^ k := by
        field_simp

end ThLean.W.S648

import ThLean.BP.SA.Convergence

noncomputable section

open Filter
open scoped Topology

namespace ThLean.W.SA08

open ThresholdFoundations ThLean.BP.SA

/-- Upper uniform-model convergence, assuming the finite transfer and domain leaves. -/
theorem SA_C64bStatement_of_deps
    (h52 : SA_X52aStatement)
    (h51a : SA_X51aStatement)
    (h51b : SA_X51bStatement)
    (h53 : SA_X53Statement)
    (h59 : SA_X59aStatement)
    (h00 : SA_F00Statement)
    (h01 : SA_F01Statement) : SA_C64bStatement := by
  intro q hq Λ α hΛ hα hproc
  have hΛpos : 0 < Λ := ((h01 q hq).2.2 Λ hΛ).1
  have hαΛ : α < Λ := by linarith [hα.2]
  have hαnonneg : 0 ≤ α := by linarith [hα.1]
  have hsimple_nonneg : ∀ c : ℝ, 0 ≤ c → ∀ᶠ n : ℕ in atTop,
      0 ≤ simpleProbability (V := Fin n) q (Nat.floor (c * n)) := by
    intro c hc
    filter_upwards [h59 c hc, eventually_ge_atTop (2 : ℕ)] with n hdom hn
    exact (h00.2.2.1 q n (Nat.floor (c * n)) (by omega) hn hdom.1).1
  have hbelow : ∀ c : ℝ, α < c → c < Λ →
      Tendsto (fun n : ℕ => simpleProbability (V := Fin n) q (Nat.floor (c * n)))
        atTop (𝓝 0) := by
    intro c hcα hcΛ
    have hc0 : 0 ≤ c := by linarith [hα.1]
    obtain ⟨N, hN, hlarge⟩ := h51b Λ hΛpos.le
    have htransfer : ∀ᶠ n : ℕ in atTop,
        simpleProbability (V := Fin n) q (Nat.floor (c * n)) ≤
          Real.exp (2 * Λ ^ 2 + 1) *
            processSurvival (V := Fin n) q (Nat.floor (c * n)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn2 : 2 ≤ n := hN.trans hn
      have hlin := hlarge n hn
      let m : ℕ := Nat.floor (c * n)
      have hmΛ : (m : ℝ) ≤ Λ * n := by
        dsimp [m]
        calc
          (Nat.floor (c * (n : ℝ)) : ℝ) ≤ c * n :=
            Nat.floor_le (mul_nonneg hc0 (Nat.cast_nonneg n))
          _ ≤ Λ * n := mul_le_mul_of_nonneg_right hcΛ.le (Nat.cast_nonneg n)
      obtain ⟨hmvalid, hbirthday⟩ :=
        h51a Λ n hΛpos.le hn2 hlin.1 hlin.2 m hmΛ
      exact (h52 q n m Λ (by omega) hn2 hmvalid hbirthday).2
    have hmul : Tendsto
        (fun n : ℕ => Real.exp (2 * Λ ^ 2 + 1) *
          processSurvival (V := Fin n) q (Nat.floor (c * n)))
        atTop (𝓝 0) := by
          simpa using (hproc.2 c hcα).const_mul (Real.exp (2 * Λ ^ 2 + 1))
    exact squeeze_zero' (hsimple_nonneg c hc0) htransfer hmul
  refine ⟨?_, ?_⟩
  · intro c hc
    by_cases hcΛ : c < Λ
    · exact hbelow c hc hcΛ
    · have hΛc : Λ ≤ c := le_of_not_gt hcΛ
      let d : ℝ := (α + Λ) / 2
      have had : α < d := by dsimp [d]; linarith
      have hdΛ : d < Λ := by dsimp [d]; linarith
      have hdc : d < c := lt_of_lt_of_le hdΛ hΛc
      have hd0 : 0 ≤ d := by dsimp [d]; linarith
      have hbase := hbelow d had hdΛ
      have hmono : ∀ᶠ n : ℕ in atTop,
          simpleProbability (V := Fin n) q (Nat.floor (c * n)) ≤
            simpleProbability (V := Fin n) q (Nat.floor (d * n)) := by
        filter_upwards [h59 c (le_trans hΛpos.le hΛc),
            eventually_ge_atTop (2 : ℕ)] with n hdom hn
        have hmle : Nat.floor (d * (n : ℝ)) ≤ Nat.floor (c * (n : ℝ)) :=
          Nat.floor_mono (mul_le_mul_of_nonneg_right hdc.le (Nat.cast_nonneg n))
        exact h53 q n (Nat.floor (d * n)) (Nat.floor (c * n)) (by omega) hn hmle hdom.1
      exact squeeze_zero' (hsimple_nonneg c (le_trans hΛpos.le hΛc)) hmono hbase
  · intro c hc
    filter_upwards [h59 c hc] with n hdom
    exact hdom.1

end ThLean.W.SA08

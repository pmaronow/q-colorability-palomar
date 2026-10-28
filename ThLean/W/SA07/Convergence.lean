import ThLean.BP.SA.Convergence

noncomputable section

open Filter
open scoped Topology
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA07

theorem SA_C64aStatement_of_deps
    (h52 : ThLean.BP.SA.SA_X52aStatement)
    (h51a : ThLean.BP.SA.SA_X51aStatement)
    (h51b : ThLean.BP.SA.SA_X51bStatement)
    (hF00 : ThLean.BP.SA.SA_F00Statement)
    (hF01 : ThLean.BP.SA.SA_F01Statement) :
    ThLean.BP.SA.SA_C64aStatement := by
  intro q hq Λ α hΛ hα hProcess c hc0 hcα
  rcases hF00 with ⟨_, _, hSimpleBounds, _⟩
  have hqOne : 1 ≤ q := by omega
  have hgamma : (1 : ℝ) ≤ gamma q := (hF01 q hq).2.1
  have hΛnonneg : 0 ≤ Λ := by linarith
  have hcΛ : c < Λ := by linarith [hα.2]
  obtain ⟨n₀, hn₀, hlarge⟩ := h51b Λ hΛnonneg
  let m : ℕ → ℕ := fun n => Nat.floor (c * (n : ℝ))
  let p : ℕ → ℝ := fun n => processSurvival (V := Fin n) q (m n)
  let s : ℕ → ℝ := fun n => simpleProbability (V := Fin n) q (m n)
  let C : ℝ := Real.exp (2 * Λ ^ 2 + 1)

  have hmBound (n : ℕ) : (m n : ℝ) ≤ Λ * (n : ℝ) := by
    dsimp [m]
    calc
      ((Nat.floor (c * (n : ℝ)) : ℕ) : ℝ) ≤ c * (n : ℝ) :=
        Nat.floor_le (mul_nonneg hc0 (Nat.cast_nonneg n))
      _ ≤ Λ * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (le_of_lt hcΛ) (Nat.cast_nonneg n)

  have hfinite : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ m n ≤ n.choose 2 ∧
        Real.exp (-2 * Λ ^ 2 - 1) ≤ ThLean.BP.SA.distinctProbability n (m n) := by
    filter_upwards [eventually_atTop.2 ⟨n₀, fun n hn => hn⟩] with n hn
    have hsize := hlarge n hn
    have hbirthday := h51a Λ n hΛnonneg (le_trans hn₀ hn) hsize.1 hsize.2
      (m n) (hmBound n)
    exact ⟨le_trans hn₀ hn, hbirthday.1, hbirthday.2⟩

  have hsLower : ∀ᶠ n : ℕ in atTop, 1 - C * (1 - p n) ≤ s n := by
    filter_upwards [hfinite] with n hn
    have hcompare := h52 q n (m n) Λ (by omega) hn.1 hn.2.1 hn.2.2
    dsimp [C, p, s] at hcompare ⊢
    linarith [hcompare.1]

  have hsUpper : ∀ᶠ n : ℕ in atTop, s n ≤ 1 := by
    filter_upwards [hfinite] with n hn
    exact (hSimpleBounds q n (m n) hqOne hn.1 hn.2.1).2

  have hp : Tendsto p atTop (𝓝 1) := by
    simpa [p, m] using hProcess.1 c hc0 hcα
  have honeConst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have honeMinusP : Tendsto (fun n : ℕ => 1 - p n) atTop (𝓝 0) := by
    simpa using honeConst.sub hp
  have hCconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
  have hscaled : Tendsto (fun n : ℕ => C * (1 - p n)) atTop (𝓝 0) := by
    simpa using hCconst.mul honeMinusP
  have hnearOne : Tendsto (fun n : ℕ => 1 - C * (1 - p n)) atTop (𝓝 1) := by
    simpa using honeConst.sub hscaled
  have hone := honeConst
  have hs : Tendsto s atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hnearOne hone hsLower hsUpper
  simpa [s, m] using hs

end ThLean.W.SA07

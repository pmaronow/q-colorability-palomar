module

public import ThLean.BP.SA.Convergence

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace ThLean.W.SA10

open ThLean.BP.SA
open ThresholdFoundations

theorem SA_C65bStatement_of_deps
    (h55 : SA_X55Statement)
    (h58b : SA_X58bStatement)
    (h59b : SA_X59bStatement)
    (hF00 : SA_F00Statement) :
    SA_C65bStatement := by
  intro q hq α hα hSimple d hd
  have hd0 : 0 ≤ d := by linarith
  have hgap : α < d / 2 := by linarith
  obtain ⟨c, hαc, hcd⟩ := exists_between hgap
  have hc0 : 0 ≤ c := by linarith

  have hfloor_event : ∀ᶠ n : ℕ in atTop, Nat.floor (c * n) ≤ n.choose 2 := by
    let N : ℕ := max 2 (Nat.ceil (2 * c) + 1)
    have hN : ∀ᶠ n : ℕ in atTop, N ≤ n :=
      eventually_atTop.2 ⟨N, fun n hn => hn⟩
    filter_upwards [hN] with n hn
    have hn2 : 2 ≤ n := le_trans (Nat.le_max_left 2 (Nat.ceil (2 * c) + 1)) hn
    have hceil : Nat.ceil (2 * c) + 1 ≤ n :=
      le_trans (Nat.le_max_right 2 (Nat.ceil (2 * c) + 1)) hn
    have hceil' : (Nat.ceil (2 * c) : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hceil
    have hcceil : 2 * c ≤ (Nat.ceil (2 * c) : ℝ) := Nat.le_ceil _
    have hcn : 2 * c ≤ (n : ℝ) - 1 := by linarith
    have hprod : (2 * c) * (n : ℝ) ≤ ((n : ℝ) - 1) * n :=
      mul_le_mul_of_nonneg_right hcn (Nat.cast_nonneg n)
    have hlinear : c * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      nlinarith [hprod]
    have hchoose : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      rw [Nat.cast_choose_two]
    have hfloor : ((Nat.floor (c * n) : ℕ) : ℝ) ≤ c * n :=
      Nat.floor_le (mul_nonneg hc0 (Nat.cast_nonneg n))
    exact_mod_cast (hfloor.trans (hlinear.trans_eq hchoose.symm))

  have hgood : ∀ᶠ n : ℕ in atTop,
      0 < n ∧ d ≤ (n : ℝ) ∧ Nat.floor (c * n) ≤ n.choose 2 := by
    filter_upwards [h59b d hd0, eventually_ge_atTop 2, hfloor_event]
      with n hdomain hn2 hfloor
    exact ⟨hdomain.1, hdomain.2, hfloor⟩

  have hbern_nonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ bernoulliProbability (V := Fin n) q (d / n) := by
    filter_upwards [hgood, eventually_ge_atTop 2] with n hn hn2
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hp0 : 0 ≤ d / (n : ℝ) := div_nonneg hd0 hn0.le
    have hp1 : d / (n : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hn0]
      nlinarith [hn.2.1]
    exact (hF00.2.2.2 q n (by omega) hn2 (d / (n : ℝ)) hp0 hp1).1

  have hbern_le : ∀ᶠ n : ℕ in atTop,
      bernoulliProbability (V := Fin n) q (d / n) ≤
        simpleProbability (V := Fin n) q (Nat.floor (c * n)) +
          binomialEvent (n.choose 2) (d / n) (fun k => k < Nat.floor (c * n)) := by
    filter_upwards [hgood, eventually_ge_atTop 2] with n hn hn2
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hp0 : 0 ≤ d / (n : ℝ) := div_nonneg hd0 hn0.le
    have hp1 : d / (n : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hn0]
      nlinarith [hn.2.1]
    exact (h55 q n (Nat.floor (c * n)) (by omega) hn2 hn.2.2
      (d / (n : ℝ)) hp0 hp1).2

  have hbern_lim : Tendsto (fun n : ℕ => bernoulliProbability (V := Fin n) q (d / n))
      atTop (𝓝 0) := by
    apply squeeze_zero' hbern_nonneg hbern_le
    have hs := hSimple.2 c hαc
    have ht := (h58b d hd0).2 c hc0 hcd
    simpa using hs.add ht

  apply hbern_lim.congr'
  filter_upwards [hgood] with n hn
  simp [sparseProbability, hn.1, hd0, hn.2.1]

end ThLean.W.SA10

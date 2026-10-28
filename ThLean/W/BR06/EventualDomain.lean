import ThLean.Defs.Bridge

noncomputable section

open Filter
open scoped Topology

namespace ThLean.W.BR06

theorem EventualDomainStatement_holds :
    ThresholdFoundations.EventualDomainStatement := by
  constructor
  · intro c hc
    let N : ℕ := max 2 (Nat.ceil (2 * c) + 1)
    have hN : ∀ᶠ n : ℕ in atTop, N ≤ n :=
      eventually_atTop.2 ⟨N, fun n hn => hn⟩
    filter_upwards [hN] with n hn using by
      constructor
      · have hn2 : 2 ≤ n := le_trans (Nat.le_max_left 2 (Nat.ceil (2 * c) + 1)) hn
        have hceil : Nat.ceil (2 * c) + 1 ≤ n :=
          le_trans (Nat.le_max_right 2 (Nat.ceil (2 * c) + 1)) hn
        have hcn : 2 * c ≤ (n : ℝ) - 1 := by
          have hceil' : (Nat.ceil (2 * c) : ℝ) + 1 ≤ (n : ℝ) := by
            exact_mod_cast hceil
          have hcceil : 2 * c ≤ (Nat.ceil (2 * c) : ℝ) := Nat.le_ceil _
          linarith
        have hprod : (2 * c) * (n : ℝ) ≤ ((n : ℝ) - 1) * n :=
          mul_le_mul_of_nonneg_right hcn (Nat.cast_nonneg n)
        have hlinear : c * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
          nlinarith [hprod]
        have hchoose : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
          rw [Nat.cast_choose_two]
        have hfloor : ((Nat.floor (c * n) : ℕ) : ℝ) ≤ c * n :=
          Nat.floor_le (mul_nonneg hc (Nat.cast_nonneg n))
        exact_mod_cast (hfloor.trans (hlinear.trans_eq hchoose.symm))
      · exact Int.natCast_floor_eq_floor (mul_nonneg hc (Nat.cast_nonneg n))
  · constructor
    · intro d hd
      let N : ℕ := max 1 (Nat.ceil d)
      have hN : ∀ᶠ n : ℕ in atTop, N ≤ n :=
        eventually_atTop.2 ⟨N, fun n hn => hn⟩
      filter_upwards [hN] with n hn using by
        constructor
        · have h1 : 1 ≤ n := le_trans (Nat.le_max_left 1 (Nat.ceil d)) hn
          omega
        · have hceil : Nat.ceil d ≤ n := le_trans (Nat.le_max_right 1 (Nat.ceil d)) hn
          exact (Nat.le_ceil d).trans (Nat.cast_le.2 hceil)
    · intro q α β hq hα hβ hαlim hβlim
      rcases hαlim with ⟨hαbelow, hαabove⟩
      rcases hβlim with ⟨hβbelow, hβabove⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with hαβ | hβα
      · let c : ℝ := (α + β) / 2
        have hc0 : 0 ≤ c := by
          have hαlo : (1 / 2 : ℝ) ≤ α := hα.1
          dsimp [c]
          linarith
        have hαc : α < c := by dsimp [c]; linarith
        have hcβ : c < β := by dsimp [c]; linarith
        have hlim0 := hαabove c hαc
        have hlim1 := hβbelow c hc0 hcβ
        have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique hlim0 hlim1
        norm_num at h01
      · let c : ℝ := (β + α) / 2
        have hc0 : 0 ≤ c := by
          have hβlo : (1 / 2 : ℝ) ≤ β := hβ.1
          dsimp [c]
          linarith
        have hβc : β < c := by dsimp [c]; linarith
        have hcα : c < α := by dsimp [c]; linarith
        have hlim0 := hβabove c hβc
        have hlim1 := hαbelow c hc0 hcα
        have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique hlim0 hlim1
        norm_num at h01

example : ThresholdFoundations.EventualDomainStatement :=
  EventualDomainStatement_holds

end ThLean.W.BR06

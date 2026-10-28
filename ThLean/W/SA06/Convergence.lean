import ThLean.BP.SA.Convergence

noncomputable section
open Filter
open scoped Topology
open ThresholdFoundations

namespace ThLean.W.SA06

/-- The upper process law follows from the upper quantile estimate and
projective monotonicity. -/
theorem SA_C63bStatement_of_deps
    (hF00 : ThLean.BP.SA.SA_F00Statement)
    (hF02 : ThLean.BP.SA.SA_F02Statement)
    (hProjective : ThresholdFoundations.ProjectiveConsistencyStatement) :
    ThLean.BP.SA.SA_C63bStatement := by
  intro q hq Λ α hΛ hα hQuantiles c hc
  have hαΛ : α < Λ := by
    have hγ : α ≤ gamma q := hα.2
    linarith

  have hnonneg : ∀ x : ℝ, ∀ᶠ n : ℕ in atTop,
      0 ≤ processSurvival (V := Fin n) q (Nat.floor (x * n)) := by
    intro x
    filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
    exact (hF00.2.1 q n (by omega) hn (Nat.floor (x * n))).1

  have hinside : ∀ x : ℝ, α < x → x < Λ →
      Tendsto (fun n : ℕ => processSurvival (V := Fin n) q (Nat.floor (x * n)))
        atTop (𝓝 0) := by
    intro x hαx hxΛ
    let d : ℝ := (α + x) / 2
    have hαd : α < d := by dsimp [d]; linarith
    have hdx : d < x := by dsimp [d]; linarith
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [hnonneg x] with n hn
      linarith
    · intro b hb
      let η : ℝ := min (etaZero Λ) (min (1 / 2 : ℝ) (b / 2))
      have hηpos : 0 < η := by
        dsimp [η, etaZero]
        positivity
      have hηcap : η ≤ etaZero Λ := by
        dsimp [η]
        exact min_le_left _ _
      have hηhalf : η ≤ 1 / 2 := by
        dsimp [η]
        exact (min_le_right _ _).trans (min_le_left _ _)
      have hηb : η < b := by
        dsimp [η]
        have hηb' : min (etaZero Λ) (min (1 / 2 : ℝ) (b / 2)) ≤ b / 2 :=
          (min_le_right _ _).trans (min_le_right _ _)
        linarith
      obtain ⟨_, hU⟩ := hQuantiles η hηpos hηcap
      have hratio : ∀ᶠ n : ℕ in atTop,
          (upperLocation q Λ η n : ℝ) / n < d :=
        (tendsto_order.1 hU).2 d hαd
      have hscale : Tendsto (fun n : ℕ => (x - d) * (n : ℝ)) atTop atTop := by
        exact (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (sub_pos.mpr hdx)
      have hgap : ∀ᶠ n : ℕ in atTop, 1 ≤ (x - d) * (n : ℝ) :=
        (tendsto_atTop.1 hscale) 1
      have hlarge : ∀ᶠ n : ℕ in atTop, 2 * q ≤ n :=
        eventually_atTop.2 ⟨2 * q, fun n hn => hn⟩
      have hfloor : ∀ᶠ n : ℕ in atTop,
          upperLocation q Λ η n < Nat.floor (x * n) := by
        filter_upwards [hratio, hgap, hlarge] with n hratio hgap hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by
          exact_mod_cast (Nat.zero_lt_of_lt (by omega : 0 < n))
        have hUn : (upperLocation q Λ η n : ℝ) < d * n :=
          (div_lt_iff₀ hnpos).1 hratio
        have hstep : ((upperLocation q Λ η n + 1 : ℕ) : ℝ) ≤ x * n := by
          apply le_of_lt
          calc
            ((upperLocation q Λ η n + 1 : ℕ) : ℝ) < d * n + 1 := by
              push_cast
              linarith
            _ ≤ d * n + (x - d) * n := by
              simpa [add_comm] using add_le_add_left hgap (d * n)
            _ = x * n := by ring
        have hstepFloor : upperLocation q Λ η n + 1 ≤ Nat.floor (x * n) :=
          Nat.le_floor hstep
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hstepFloor
      have hsurvival : ∀ᶠ n : ℕ in atTop,
          processSurvival (V := Fin n) q (Nat.floor (x * n)) < η := by
        filter_upwards [hfloor, hlarge] with n hfloor hn
        have hcap : upperLocation q Λ η n < cap Λ n := by
          unfold cap
          exact lt_of_lt_of_le hfloor <| Nat.floor_mono <|
            mul_le_mul_of_nonneg_right hxΛ.le (Nat.cast_nonneg n)
        exact hF02 q hq Λ η hΛ hηpos hηhalf n hn hcap
          (Nat.floor (x * n)) hfloor
      filter_upwards [hsurvival] with n hn
      exact lt_trans hn hηb

  by_cases hcΛ : c < Λ
  · exact hinside c hc hcΛ
  · have hΛc : Λ ≤ c := le_of_not_gt hcΛ
    let c' : ℝ := (α + Λ) / 2
    have hαc' : α < c' := by dsimp [c']; linarith
    have hc'Λ : c' < Λ := by dsimp [c']; linarith
    have hc'c : c' ≤ c := (le_of_lt hc'Λ).trans hΛc
    have hsmall := hinside c' hαc' hc'Λ
    have hcompare : ∀ᶠ n : ℕ in atTop,
        processSurvival (V := Fin n) q (Nat.floor (c * n)) ≤
          processSurvival (V := Fin n) q (Nat.floor (c' * n)) := by
      filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
      have hfloor : Nat.floor (c' * n) ≤ Nat.floor (c * n) :=
        Nat.floor_mono <| mul_le_mul_of_nonneg_right hc'c (Nat.cast_nonneg n)
      exact (hProjective.2 q n (by omega) hn).1 hfloor
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [hnonneg c] with n hn
      linarith
    · intro b hb
      have hupper := (tendsto_order.1 hsmall).2 b hb
      filter_upwards [hcompare, hupper] with n hmono hup
      exact lt_of_le_of_lt hmono hup

example (hF00 : ThLean.BP.SA.SA_F00Statement)
    (hF02 : ThLean.BP.SA.SA_F02Statement)
    (hProjective : ThresholdFoundations.ProjectiveConsistencyStatement) :
    ThLean.BP.SA.SA_C63bStatement :=
  SA_C63bStatement_of_deps hF00 hF02 hProjective

end ThLean.W.SA06

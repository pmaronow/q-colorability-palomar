import ThLean.BP.SA.Convergence

noncomputable section

open Filter
open scoped Topology

namespace ThLean.W.SA05

open ThresholdFoundations ThLean.BP.SA

private theorem eventually_floor_le_lowerLocation
    (q : ℕ) (Λ α η c : ℝ) (hlim : QuantileLimits q Λ α)
    (hη : 0 < η) (hη₀ : η ≤ etaZero Λ)
    (hc : 0 ≤ c) (hcα : c < α) :
    ∀ᶠ n : ℕ in atTop,
      Nat.floor (c * (n : ℝ)) ≤ lowerLocation q Λ η n := by
  have hlow := (hlim η hη hη₀).1
  let t : ℝ := (c + α) / 2
  have hct : c < t := by dsimp [t]; linarith
  have htα : t < α := by dsimp [t]; linarith
  have hratio : ∀ᶠ n : ℕ in atTop,
      t < (lowerLocation q Λ η n : ℝ) / (n : ℝ) :=
    hlow.eventually (Ioi_mem_nhds htα)
  filter_upwards [hratio, Filter.eventually_ge_atTop 2] with n hnratio hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hcnL : c * (n : ℝ) < (lowerLocation q Λ η n : ℝ) :=
    (lt_div_iff₀ hnpos).1 (lt_trans hct hnratio)
  have hfloor : ((Nat.floor (c * (n : ℝ)) : ℕ) : ℝ) ≤ c * (n : ℝ) :=
    Nat.floor_le (by positivity)
  exact_mod_cast (le_of_lt (lt_of_le_of_lt hfloor hcnL))

theorem SA_C63aStatement_of_deps (hF00 : SA_F00Statement)
    (hquant : PreQuantileStatement) : SA_C63aStatement := by
  intro q hq Λ α hΛ hα hlim c hc hcα
  let f : ℕ → ℝ := fun n =>
    processSurvival (V := Fin n) q (Nat.floor (c * (n : ℝ)))
  have hqR : 1 < (q : ℝ) := by
    exact_mod_cast (show 1 < q by omega)
  have hden : 0 < (q : ℝ) - 1 := by linarith
  have hratio : 1 < (q : ℝ) / ((q : ℝ) - 1) :=
    (lt_div_iff₀ hden).2 (by linarith)
  have hnumLog : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hdenLog : 0 < Real.log ((q : ℝ) / ((q : ℝ) - 1)) := Real.log_pos hratio
  have hgamma : 0 < gamma q := by
    unfold gamma
    exact div_pos hnumLog hdenLog
  have hΛpos : 0 < Λ := lt_trans (by linarith) hΛ
  have hetaPos : 0 < etaZero Λ := by
    unfold etaZero
    positivity
  have hetaSmall : etaZero Λ < (1 / 8 : ℝ) := by
    unfold etaZero
    have hexp : Real.exp (-2 * Λ) < 1 := by
      calc
        Real.exp (-2 * Λ) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    nlinarith
  have hbounds : ∀ᶠ n : ℕ in atTop, 0 ≤ f n ∧ f n ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop (2 * q)] with n hn
    have hprob := hF00.2.1 q n (by omega) (by omega) (Nat.floor (c * (n : ℝ)))
    simpa [f] using hprob
  apply tendsto_order.2
  constructor
  · intro b hb
    let η : ℝ := min (etaZero Λ / 2) ((1 - b) / 2)
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (by positivity) (by linarith)
    have hη₀ : η ≤ etaZero Λ := by
      dsimp [η]
      exact le_trans (min_le_left _ _) (by linarith)
    have hηhalf : η ≤ (1 / 2 : ℝ) := by
      dsimp [η]
      exact le_trans (min_le_left _ _) (by linarith [hetaSmall])
    have hbη : b < 1 - η := by
      dsimp [η]
      have hηb : min (etaZero Λ / 2) ((1 - b) / 2) < 1 - b :=
        lt_of_le_of_lt (min_le_right _ _) (by linarith)
      linarith
    have hfloor := eventually_floor_le_lowerLocation q Λ α η c hlim hη hη₀ hc hcα
    filter_upwards [hfloor, Filter.eventually_ge_atTop (2 * q)] with n hnfloor hn
    have hpre := hquant q n (cap Λ n) hq (by omega) η hη hηhalf
    have hsurv : 1 - η < f n := by
      have htail := hpre.2.2.2.2.2.2.1
      have hlow : 1 - η < processSurvival (V := Fin n) q
          (Nat.floor (c * (n : ℝ))) :=
        htail _ (by simpa [lowerLocation] using hnfloor)
      simpa [f] using hlow
    exact lt_trans hbη hsurv
  · intro b hb
    filter_upwards [hbounds] with n hn
    exact lt_of_le_of_lt hn.2 hb

example (hF00 : SA_F00Statement) (hquant : PreQuantileStatement) :
    SA_C63aStatement := SA_C63aStatement_of_deps hF00 hquant

end ThLean.W.SA05

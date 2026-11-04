module

public import ThLean.BP.SA.Convergence

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA02
open ThresholdFoundations

/-- The centre estimates pass to any limit of the normalized lower quantiles. -/
theorem SA_C61aStatement_of_deps (hcentre : PreCentreStatement) :
    ThLean.BP.SA.SA_C61aStatement := by
  intro q hq Λ η α hΛ hη hηhalf hlim
  have hpc := hcentre q hq Λ hΛ η hη hηhalf
  have hlow : ∀ c : ℝ, 0 < c → c < 1 / 2 → c ≤ α := by
    intro c hc hcHalf
    obtain ⟨C, hC, hprob, hevent⟩ := hpc.2.2 c hc hcHalf
    have hnpos : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
      Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩
    have hevent' : ∀ᶠ n : ℕ in atTop, c ≤ xi q Λ η n := by
      filter_upwards [hevent, hnpos] with n hn hnpos
      have hnreal : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [xi]
      exact le_of_lt ((lt_div_iff₀ hnreal).2 hn)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hevent'
  have hupp : ∀ β : ℝ, gamma q < β → α ≤ β := by
    intro β hβ
    have hevent : ∀ᶠ n : ℕ in atTop,
        lowerLocation q Λ η n ≤ upperLocation q Λ η n ∧
          (upperLocation q Λ η n : ℝ) ≤ β * n := by
      filter_upwards [hpc.2.1 β hβ] with n hn
      exact ⟨hn.1, hn.2.1⟩
    have hnpos : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
      Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩
    have hevent' : ∀ᶠ n : ℕ in atTop, xi q Λ η n ≤ β := by
      filter_upwards [hevent, hnpos] with n hn hnpos
      have hnreal : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [xi]
      apply (div_le_iff₀ hnreal).2
      exact le_trans (Nat.cast_le.mpr hn.1) hn.2
    exact le_of_tendsto hlim hevent'
  constructor
  · by_contra hnot
    have hαhalf : α < 1 / 2 := lt_of_not_ge hnot
    by_cases hαneg : α < 0
    · have h := hlow (1 / 4) (by norm_num) (by norm_num)
      linarith
    · have hαnonneg : 0 ≤ α := le_of_not_gt hαneg
      let c : ℝ := (α + 1 / 2) / 2
      have hc : 0 < c := by dsimp [c]; linarith
      have hcHalf : c < 1 / 2 := by dsimp [c]; linarith
      have h := hlow c hc hcHalf
      dsimp [c] at h
      linarith
  · by_contra hnot
    have hαgamma : gamma q < α := lt_of_not_ge hnot
    let β : ℝ := (gamma q + α) / 2
    have hβ : gamma q < β := by dsimp [β]; linarith
    have hβα : β < α := by dsimp [β]; linarith
    have h := hupp β hβ
    dsimp [β] at h
    linarith

end ThLean.W.SA02

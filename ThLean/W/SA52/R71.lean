import ThLean.BP.SA.Alternatives
import ThLean.BP.SA.Basics
import ThLean.BP.SA.Quantiles
import ThLean.W.SA52.Poisson

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 600000

namespace ThLean.W.SA52
open ThresholdFoundations

theorem SA_R71Statement_of_deps
    (h20 : ThLean.BP.SA.SA_Q20Statement)
    (hF02 : ThLean.BP.SA.SA_F02Statement)
    (hMom : ThLean.BP.SA.SA_E01bStatement)
    (hCheb : ThLean.BP.SA.SA_X57Statement)
    (hPre : ThresholdFoundations.PreQuantileStatement) :
    ThLean.BP.SA.SA_R71Statement := by
  intro q n hq hn Λ η c hΛ hη hηhalf hc hcΛ
  have hnLarge : 6 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hqden : 0 < (q : ℝ) - 1 := by linarith
  have hratio : 1 < (q : ℝ) / ((q : ℝ) - 1) :=
    (lt_div_iff₀ hqden).2 (by linarith)
  have hgamma : 0 < gamma q := by
    unfold gamma
    exact div_pos (Real.log_pos hqR) (Real.log_pos hratio)
  have hΛpos : 0 < Λ := by linarith
  have hpre' := hPre q n (cap Λ n) hq hn2 η hη hηhalf
  rcases hpre' with ⟨hLU, hUcap, hCDF, hTail, hCapTail, hCapCDF, hbelow, habove⟩
  let L := lowerLocation q Λ η n
  let U := upperLocation q Λ η n
  let μ : ℝ := c * ((n : ℝ) - 1)
  let eps : ℝ := Λ / (Real.log (n : ℝ)) ^ 2
  let low : Set ℕ := {j | j ≤ L}
  let high : Set ℕ := {j | j ≤ U}
  let P := ProbabilityTheory.poissonMeasure μ.toNNReal
  have hμ : 0 ≤ μ := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 1 ≤ n by omega)
    dsimp [μ]
    exact mul_nonneg hc.le (by linarith)
  have hmixData := h20 q n (by omega) hn2 c hc.le
  rcases hmixData with ⟨hsumMix, hmixNonneg, hmixLe, hrho⟩
  refine ⟨?_, ?_⟩
  · intro hBelow
    have hlowMass : 1 - eps ≤ P.real low := by
      have hsubset : lowᶜ ⊆ {j : ℕ | (poissonDeviation n : ℝ) ≤
          |(j : ℝ) - μ|} := by
        intro j hj
        have hjNat : L < j := by simpa [low] using hj
        have hjReal : (L : ℝ) < (j : ℝ) := by exact_mod_cast hjNat
        have hloc : μ ≤ (L : ℝ) - poissonDeviation n := by
          simpa [L, μ] using hBelow
        have hle : (poissonDeviation n : ℝ) ≤ (j : ℝ) - μ := by linarith
        change (poissonDeviation n : ℝ) ≤ |(j : ℝ) - μ|
        rw [abs_of_nonneg (by linarith : 0 ≤ (j : ℝ) - μ)]
        exact hle
      have htail : P.real lowᶜ ≤ eps := by
        calc
          P.real lowᶜ ≤ P.real {j : ℕ | (poissonDeviation n : ℝ) ≤
              |(j : ℝ) - μ|} := measureReal_mono hsubset (by finiteness)
          _ ≤ eps := by
            simpa [P, μ, eps] using
              (poissonChebyshev_scaled_bound hMom hCheb n hnLarge Λ c hΛpos hc hcΛ)
      have hcomp : P.real lowᶜ = 1 - P.real low := by
        simpa [P] using poissonEventMass_compl μ hμ low
      rw [hcomp] at htail
      linarith
    have hlowCutSummable : Summable (fun j : ℕ => poissonWeight μ j *
        (if j ∈ low then 1 - η else 0)) := by
      apply poissonCutoffSummable μ hμ low (1 - η) 0
      · linarith
      · norm_num
      · linarith
      · norm_num
    have hlowCut : (∑' j : ℕ, poissonWeight μ j *
        (if j ∈ low then 1 - η else 0)) = (1 - η) * P.real low := by
      have h := poissonWeightedCutoff μ hμ low (1 - η) 0 (by linarith) (by norm_num)
        (by linarith) (by norm_num)
      simpa [P] using h
    have hpointLow (j : ℕ) : poissonWeight μ j * (if j ∈ low then 1 - η else 0) ≤
        poissonWeight μ j * processSurvival (V := Fin n) q j := by
      by_cases hj : j ∈ low
      · have hsurv := hbelow j (by simpa [L, low, lowerLocation] using hj)
        rw [if_pos hj]
        exact mul_le_mul_of_nonneg_left hsurv.le (poissonWeight_nonneg μ hμ j)
      · rw [if_neg hj]
        simpa using mul_nonneg (poissonWeight_nonneg μ hμ j)
          (processSurvivalBounds q n j hn2).1
    have hmixLow : (∑' j : ℕ, poissonWeight μ j *
        (if j ∈ low then 1 - η else 0)) ≤
        poissonMixture μ (fun j => processSurvival (V := Fin n) q j) := by
      rw [poissonMixture]
      exact Summable.tsum_le_tsum hpointLow hlowCutSummable hsumMix
    have hmixLower : (1 - η) * (1 - eps) ≤
        poissonMixture μ (fun j => processSurvival (V := Fin n) q j) := by
      calc
        (1 - η) * (1 - eps) ≤ (1 - η) * P.real low :=
          mul_le_mul_of_nonneg_left hlowMass (by linarith)
        _ = ∑' j : ℕ, poissonWeight μ j * (if j ∈ low then 1 - η else 0) := hlowCut.symm
        _ ≤ poissonMixture μ (fun j => processSurvival (V := Fin n) q j) := hmixLow
    have hBelowTarget : Real.exp (-Λ) * (1 - η) * (1 - eps) ≤ rho q n c := by
      by_cases heps : eps ≤ 1
      · have hfactor : 0 ≤ (1 - η) * (1 - eps) :=
          mul_nonneg (by linarith) (by linarith)
        have hexp : Real.exp (-Λ) ≤ Real.exp (-c) :=
          Real.exp_le_exp.mpr (by linarith)
        calc
          Real.exp (-Λ) * (1 - η) * (1 - eps) ≤
              Real.exp (-c) * ((1 - η) * (1 - eps)) := by
            nlinarith [mul_le_mul_of_nonneg_right hexp hfactor]
          _ ≤ Real.exp (-c) * poissonMixture μ
              (fun j => processSurvival (V := Fin n) q j) :=
            mul_le_mul_of_nonneg_left hmixLower (Real.exp_pos (-c)).le
          _ = rho q n c := by simpa [μ] using hrho.symm
      · have hfactor : (1 - η) * (1 - eps) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        have hrhoNonneg : 0 ≤ rho q n c := by
          rw [hrho]
          exact mul_nonneg (Real.exp_pos (-c)).le hmixNonneg
        have htarget : Real.exp (-Λ) * (1 - η) * (1 - eps) ≤ 0 := by
          have hprod := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-Λ)).le hfactor
          nlinarith [hprod]
        exact htarget.trans hrhoNonneg
    simpa [eps] using hBelowTarget
  · intro hUcapLeaf hAbove
    have hUcap' : U < cap Λ n := by simpa [U] using hUcapLeaf
    have hupperMass : P.real high ≤ eps := by
      have hsubset : high ⊆ {j : ℕ | (poissonDeviation n : ℝ) ≤
          |(j : ℝ) - μ|} := by
        intro j hj
        have hjNat : j ≤ U := by simpa [high] using hj
        have hjReal : (j : ℝ) ≤ (U : ℝ) := by exact_mod_cast hjNat
        have hloc : (U : ℝ) + poissonDeviation n ≤ μ := by
          simpa [U, μ] using hAbove
        have hle : (poissonDeviation n : ℝ) ≤ μ - (j : ℝ) := by linarith
        change (poissonDeviation n : ℝ) ≤ |(j : ℝ) - μ|
        rw [abs_of_nonpos (by linarith : (j : ℝ) - μ ≤ 0)]
        linarith
      calc
        P.real high ≤ P.real {j : ℕ | (poissonDeviation n : ℝ) ≤
            |(j : ℝ) - μ|} := measureReal_mono hsubset (by finiteness)
        _ ≤ eps := by
          simpa [P, μ, eps] using
            (poissonChebyshev_scaled_bound hMom hCheb n hnLarge Λ c hΛpos hc hcΛ)
    have hhighCutSummable : Summable (fun j : ℕ => poissonWeight μ j *
        (if j ∈ high then 1 else η)) := by
      apply poissonCutoffSummable μ hμ high 1 η
      · norm_num
      · linarith
      · norm_num
      · linarith
    have hhighCut : (∑' j : ℕ, poissonWeight μ j *
        (if j ∈ high then 1 else η)) = P.real high + η * P.real highᶜ := by
      simpa [P, one_mul] using
        (poissonWeightedCutoff μ hμ high 1 η (by norm_num) hη.le (by norm_num)
          (le_trans hηhalf (by norm_num)))
    have hpointHigh (j : ℕ) : poissonWeight μ j * processSurvival (V := Fin n) q j ≤
        poissonWeight μ j * (if j ∈ high then 1 else η) := by
      by_cases hj : j ∈ high
      · rw [if_pos hj]
        exact mul_le_mul_of_nonneg_left (processSurvivalBounds q n j hn2).2
          (poissonWeight_nonneg μ hμ j)
      · have hjNat : U < j := by simpa [high] using hj
        have hsurv : processSurvival (V := Fin n) q j < η :=
          hF02 q hq Λ η hΛ hη hηhalf n hn (by simpa [U] using hUcap') j
            (by simpa [U] using hjNat)
        rw [if_neg hj]
        exact mul_le_mul_of_nonneg_left hsurv.le (poissonWeight_nonneg μ hμ j)
    have hmixHigh : poissonMixture μ (fun j => processSurvival (V := Fin n) q j) ≤
        ∑' j : ℕ, poissonWeight μ j * (if j ∈ high then 1 else η) := by
      rw [poissonMixture]
      exact Summable.tsum_le_tsum hpointHigh hsumMix hhighCutSummable
    have hmixUpper : poissonMixture μ (fun j => processSurvival (V := Fin n) q j) ≤ eps + η := by
      calc
        poissonMixture μ (fun j => processSurvival (V := Fin n) q j) ≤
            ∑' j : ℕ, poissonWeight μ j * (if j ∈ high then 1 else η) := hmixHigh
        _ = P.real high + η * P.real highᶜ := hhighCut
        _ ≤ eps + η := by
          have hcomp := poissonEventMass_le_one μ hμ highᶜ
          calc
            P.real high + η * P.real highᶜ ≤ eps + η * 1 :=
              add_le_add hupperMass (mul_le_mul_of_nonneg_left hcomp hη.le)
            _ = eps + η := by ring
    have hAboveTarget : rho q n c ≤ η + eps := by
      have hexp : Real.exp (-c) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have hmixNonneg' : 0 ≤ poissonMixture μ
          (fun j => processSurvival (V := Fin n) q j) := by simpa [μ] using hmixNonneg
      calc
        rho q n c = Real.exp (-c) * poissonMixture μ
            (fun j => processSurvival (V := Fin n) q j) := by simpa [μ] using hrho
        _ ≤ poissonMixture μ (fun j => processSurvival (V := Fin n) q j) :=
          by
            simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right hexp hmixNonneg')
        _ ≤ eps + η := hmixUpper
        _ = η + eps := by ring
    simpa [eps] using hAboveTarget

end ThLean.W.SA52

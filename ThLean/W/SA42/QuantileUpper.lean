module

public import ThLean.BP.SA.Quantiles
public import ThLean.BP.SA.Basics

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA42

open ThresholdFoundations
open ThLean.BP.SA

private lemma poissonWeight_summable (μ : ℝ) :
    Summable (fun j : ℕ => poissonWeight μ j) := by
  have h := Real.summable_pow_div_factorial μ
  simpa [poissonWeight, mul_div_assoc] using h.mul_left (Real.exp (-μ))

private lemma tsum_poissonWeight_eq_one (μ : ℝ) :
    (∑' j : ℕ, poissonWeight μ j) = 1 := by
  calc
    (∑' j : ℕ, poissonWeight μ j) =
        Real.exp (-μ) * (∑' j : ℕ, μ ^ j / (Nat.factorial j : ℝ)) := by
          simp_rw [poissonWeight, mul_div_assoc]
          exact tsum_mul_left
    _ = 1 := by
          have hseries : (∑' j : ℕ, μ ^ j / (Nat.factorial j : ℝ)) = Real.exp μ := by
            have h := congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) μ
            calc
              (∑' j : ℕ, μ ^ j / (Nat.factorial j : ℝ)) = NormedSpace.exp μ := h.symm
              _ = Real.exp μ := (congrFun Real.exp_eq_exp_ℝ μ).symm
          rw [hseries, ← Real.exp_add]
          simp

private lemma poissonWeight_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) :
    0 ≤ poissonWeight μ j := by
  simp only [poissonWeight]
  positivity

private lemma poissonLowerTail_eq_tsum (μ a : ℝ) (hμ : 0 ≤ μ) :
    poissonLowerTail μ a =
      ∑' j : ℕ, if (j : ℝ) ≤ a then poissonWeight μ j else 0 := by
  unfold poissonLowerTail poissonLowerTailENN
  rw [ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro j
    by_cases hj : (j : ℝ) ≤ a
    · simp [hj, poissonWeight_nonneg hμ j]
    · simp [hj]
  · intro j
    split_ifs <;> simp

private lemma poissonLowerTail_summable (μ a : ℝ) (hμ : 0 ≤ μ) :
    Summable (fun j : ℕ => if (j : ℝ) ≤ a then poissonWeight μ j else 0) := by
  apply (poissonWeight_summable μ).of_nonneg_of_le
  · intro j
    split_ifs with hj
    · exact poissonWeight_nonneg hμ j
    · exact le_rfl
  · intro j
    split_ifs with hj
    · exact le_rfl
    · exact poissonWeight_nonneg hμ j

theorem SA_Q22bStatement_of_deps
    (h20 : SA_Q20Statement)
    (hF00 : SA_F00Statement)
    (hF02 : SA_F02Statement)
    (hTails : ThresholdFoundations.PreTailsStatement) :
    SA_Q22bStatement := by
  intro q n hq hn Λ η c hΛ hη hηhalf hc hcΛ hcap hmean
  let μ : ℝ := c * ((n : ℝ) - 1)
  let Δ : ℕ := poissonDeviation n
  have hn2 : 2 ≤ n := by omega
  have hnsub_pos : 0 < (n : ℝ) - 1 := by
    have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hmu_pos : 0 < μ := by
    change 0 < c * ((n : ℝ) - 1)
    exact mul_pos hc hnsub_pos
  have hmu_nonneg : 0 ≤ μ := le_of_lt hmu_pos
  have hDelta_pos : 0 < (Δ : ℝ) := by
    have hn1 : 1 < (n : ℝ) := by
      have : 2 ≤ n := hn2
      exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hprod : 0 < Real.sqrt (n : ℝ) * Real.log (n : ℝ) := mul_pos hsqrt hlog
    have hceil : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ (Δ : ℝ) := by
      dsimp [Δ, poissonDeviation]
      exact_mod_cast Nat.le_ceil (Real.sqrt (n : ℝ) * Real.log (n : ℝ))
    linarith
  have hUmean : (upperLocation q Λ η n : ℝ) ≤ μ - (Δ : ℝ) := by
    dsimp [μ, Δ]
    linarith
  obtain ⟨h20sum, h20nonneg, _, h20id⟩ :=
    h20 q n (by omega) hn2 c (le_of_lt hc)
  have hweights : Summable (fun j : ℕ => poissonWeight μ j) := poissonWeight_summable μ
  have hweightSum : (∑' j : ℕ, poissonWeight μ j) = 1 := tsum_poissonWeight_eq_one μ
  have hweightNonneg : ∀ j : ℕ, 0 ≤ poissonWeight μ j :=
    fun j => poissonWeight_nonneg hmu_nonneg j
  have hcutSummable : Summable
      (fun j : ℕ => if (j : ℝ) ≤ (upperLocation q Λ η n : ℝ)
        then poissonWeight μ j else 0) :=
    poissonLowerTail_summable μ (upperLocation q Λ η n : ℝ) hmu_nonneg
  have hpointwise : ∀ j : ℕ,
      poissonWeight μ j * processSurvival (V := Fin n) q j ≤
        η * poissonWeight μ j +
          (if (j : ℝ) ≤ (upperLocation q Λ η n : ℝ)
            then poissonWeight μ j else 0) := by
    intro j
    by_cases hj : (j : ℝ) ≤ (upperLocation q Λ η n : ℝ)
    · have hsurv := (hF00.2.1 q n (by omega) hn2 j).2
      simp [hj]
      calc
        poissonWeight μ j * processSurvival (V := Fin n) q j ≤ poissonWeight μ j :=
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsurv (hweightNonneg j)
        _ ≤ η * poissonWeight μ j + poissonWeight μ j := by
          nlinarith [mul_nonneg (le_of_lt hη) (hweightNonneg j)]
    · have hjReal : (upperLocation q Λ η n : ℝ) < (j : ℝ) := lt_of_not_ge hj
      have hjNat : upperLocation q Λ η n < j := by exact_mod_cast hjReal
      have hsurv := hF02 q hq Λ η hΛ hη hηhalf n hn hcap j hjNat
      simp [hj]
      calc
        poissonWeight μ j * processSurvival (V := Fin n) q j ≤
            poissonWeight μ j * η :=
          mul_le_mul_of_nonneg_left (le_of_lt hsurv) (hweightNonneg j)
        _ = η * poissonWeight μ j := by ring
  have hrightSummable : Summable (fun j : ℕ =>
      η * poissonWeight μ j +
        (if (j : ℝ) ≤ (upperLocation q Λ η n : ℝ)
          then poissonWeight μ j else 0)) :=
    (hweights.mul_left η).add hcutSummable
  have hmixBound : poissonMixture μ (processSurvival (V := Fin n) q) ≤
      η + poissonLowerTail μ (upperLocation q Λ η n : ℝ) := by
    calc
      poissonMixture μ (processSurvival (V := Fin n) q) =
          ∑' j : ℕ, poissonWeight μ j * processSurvival (V := Fin n) q j := rfl
      _ ≤ ∑' j : ℕ, (η * poissonWeight μ j +
            (if (j : ℝ) ≤ (upperLocation q Λ η n : ℝ)
              then poissonWeight μ j else 0)) := by
        simpa [μ] using h20sum.tsum_le_tsum hpointwise hrightSummable
      _ = η + poissonLowerTail μ (upperLocation q Λ η n : ℝ) := by
        rw [(hweights.mul_left η).tsum_add hcutSummable,
          hweights.tsum_mul_left η, hweightSum,
          poissonLowerTail_eq_tsum μ _ hmu_nonneg]
        ring
  have hLambda_pos : 0 < Λ := lt_of_lt_of_le hc hcΛ
  have hnreal_pos : 0 < (n : ℝ) := by
    have : 2 ≤ n := hn2
    exact_mod_cast (by omega : 0 < n)
  have hnreal_two : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hmu_upper : μ ≤ Λ * (n : ℝ) := by
    have hnsub : 0 ≤ (n : ℝ) - 1 := by linarith
    have hfirst : c * ((n : ℝ) - 1) ≤ Λ * ((n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hcΛ hnsub
    have hsecond : Λ * ((n : ℝ) - 1) ≤ Λ * (n : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hLambda_pos)
    change c * ((n : ℝ) - 1) ≤ Λ * (n : ℝ)
    exact le_trans hfirst hsecond
  have hDeltaSq : (n : ℝ) * Real.log (n : ℝ) ^ 2 ≤ (Δ : ℝ) ^ 2 := by
    have hn1 : 1 < (n : ℝ) := by linarith
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hbase : 0 ≤ Real.sqrt (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hsqrt (le_of_lt hlog)
    have hceil : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ (Δ : ℝ) := by
      dsimp [Δ, poissonDeviation]
      exact_mod_cast Nat.le_ceil (Real.sqrt (n : ℝ) * Real.log (n : ℝ))
    have hsq := (sq_le_sq₀ hbase (le_of_lt hDelta_pos)).2 hceil
    rw [mul_pow, Real.sq_sqrt (le_of_lt hnreal_pos)] at hsq
    nlinarith
  have hden : 2 * μ ≤ 2 * Λ * (n : ℝ) := by nlinarith [hmu_upper]
  have hexpArg : Real.log (n : ℝ) ^ 2 / (2 * Λ) ≤ (Δ : ℝ) ^ 2 / (2 * μ) := by
    have hnum : (n : ℝ) * Real.log (n : ℝ) ^ 2 /
          (2 * Λ * (n : ℝ)) ≤ (Δ : ℝ) ^ 2 / (2 * Λ * (n : ℝ)) :=
      div_le_div_of_nonneg_right hDeltaSq (by positivity)
    have hdenpos : 0 < 2 * μ := by positivity
    have hstep : (Δ : ℝ) ^ 2 / (2 * Λ * (n : ℝ)) ≤
        (Δ : ℝ) ^ 2 / (2 * μ) :=
      div_le_div₀ (sq_nonneg _) le_rfl hdenpos hden
    calc
      Real.log (n : ℝ) ^ 2 / (2 * Λ) =
          ((n : ℝ) * Real.log (n : ℝ) ^ 2) / (2 * Λ * (n : ℝ)) := by
            field_simp [ne_of_gt hLambda_pos, ne_of_gt hnreal_pos]
      _ ≤ (Δ : ℝ) ^ 2 / (2 * Λ * (n : ℝ)) := hnum
      _ ≤ (Δ : ℝ) ^ 2 / (2 * μ) := hstep
  have htail := hTails.2.2.1 μ (Δ : ℝ) hmu_pos hDelta_pos
  have htailMono : poissonLowerTail μ (upperLocation q Λ η n : ℝ) ≤
      poissonLowerTail μ (μ - (Δ : ℝ)) := by
    rw [poissonLowerTail_eq_tsum μ _ hmu_nonneg,
      poissonLowerTail_eq_tsum μ _ hmu_nonneg]
    apply (poissonLowerTail_summable μ _ hmu_nonneg).tsum_le_tsum
    · intro j
      by_cases hj : (j : ℝ) ≤ (upperLocation q Λ η n : ℝ)
      · have hj' : (j : ℝ) ≤ μ - (Δ : ℝ) := le_trans hj hUmean
        simp [hj, hj']
      · by_cases hj' : (j : ℝ) ≤ μ - (Δ : ℝ)
        · simpa [hj, hj'] using poissonWeight_nonneg hmu_nonneg j
        · simp [hj, hj']
    · exact poissonLowerTail_summable μ _ hmu_nonneg
  have htailExp : Real.exp (-((Δ : ℝ) ^ 2) / (2 * μ)) ≤ poissonTailError Λ n := by
    unfold poissonTailError
    convert Real.exp_le_exp.mpr (neg_le_neg hexpArg) using 1 <;> ring_nf
  have hlowBound : poissonLowerTail μ (upperLocation q Λ η n : ℝ) ≤
      poissonTailError Λ n := by
    calc
      poissonLowerTail μ (upperLocation q Λ η n : ℝ) ≤
          poissonLowerTail μ (μ - (Δ : ℝ)) := htailMono
      _ ≤ Real.exp (-((Δ : ℝ) ^ 2) / (2 * μ)) := htail.2
      _ ≤ poissonTailError Λ n := htailExp
  have hmixed : poissonMixture μ (processSurvival (V := Fin n) q) ≤
      η + poissonTailError Λ n := by
    linarith [hmixBound, hlowBound]
  have hexp_c : Real.exp (-c) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  calc
    rho q n c = Real.exp (-c) * poissonMixture μ (processSurvival (V := Fin n) q) := by
      simpa [μ] using h20id
    _ ≤ poissonMixture μ (processSurvival (V := Fin n) q) := by
      calc
        Real.exp (-c) * poissonMixture μ (processSurvival (V := Fin n) q) ≤
            1 * poissonMixture μ (processSurvival (V := Fin n) q) :=
          mul_le_mul_of_nonneg_right hexp_c h20nonneg
        _ = poissonMixture μ (processSurvival (V := Fin n) q) := by ring
    _ ≤ η + poissonTailError Λ n := hmixed

end ThLean.W.SA42

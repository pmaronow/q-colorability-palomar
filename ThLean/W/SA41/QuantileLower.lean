import ThLean.BP.SA.Quantiles
import ThLean.BP.SA.Basics

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA41
open ThresholdFoundations

private lemma poissonWeight_nonneg_of_nonneg (z : ℝ) (hz : 0 ≤ z) (j : ℕ) :
    0 ≤ poissonWeight z j := by
  unfold poissonWeight
  positivity

private lemma poissonWeight_summable (z : ℝ) : Summable (poissonWeight z) := by
  have h := NormedSpace.expSeries_div_summable z
  have heq : (fun j : ℕ => poissonWeight z j) =
      fun j => Real.exp (-z) * (z ^ j / (Nat.factorial j : ℝ)) := by
    funext j
    simp [poissonWeight, mul_div_assoc]
  simpa only [← heq] using h.mul_left (Real.exp (-z))

private lemma poissonWeight_tsum_one (z : ℝ) :
    (∑' j : ℕ, poissonWeight z j) = 1 := by
  have hseries : (∑' j : ℕ, z ^ j / (Nat.factorial j : ℝ)) = Real.exp z := by
    have h := (NormedSpace.expSeries_div_hasSum_exp z).tsum_eq
    rw [← Real.exp_eq_exp_ℝ] at h
    exact h
  calc
    (∑' j : ℕ, poissonWeight z j) =
        Real.exp (-z) * (∑' j : ℕ, z ^ j / (Nat.factorial j : ℝ)) := by
      have heq : (fun j : ℕ => poissonWeight z j) =
          fun j => Real.exp (-z) * (z ^ j / (Nat.factorial j : ℝ)) := by
        funext j
        simp [poissonWeight, mul_div_assoc]
      rw [heq, tsum_mul_left]
    _ = Real.exp (-z) * Real.exp z := by rw [hseries]
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

private lemma poissonTail_eq_tsum (z a : ℝ) (hz : 0 ≤ z) :
    poissonTail z a =
      ∑' j : ℕ, (if a ≤ (j : ℝ) then poissonWeight z j else 0) := by
  unfold poissonTail poissonTailENN
  rw [ENNReal.tsum_toReal_eq (fun j => by
    by_cases hj : a ≤ (j : ℝ) <;> simp [hj])]
  apply tsum_congr
  intro j
  by_cases hj : a ≤ (j : ℝ)
  · simp [hj, poissonWeight_nonneg_of_nonneg z hz j]
  · simp [hj]

private lemma poissonTailSeries_summable (z a : ℝ) (hz : 0 ≤ z) :
    Summable (fun j : ℕ => if a ≤ (j : ℝ) then poissonWeight z j else 0) := by
  apply (poissonWeight_summable z).of_nonneg_of_le
  · intro j
    by_cases hj : a ≤ (j : ℝ) <;> simp [hj, poissonWeight_nonneg_of_nonneg z hz j]
  · intro j
    by_cases hj : a ≤ (j : ℝ)
    · simp [hj]
    · simp [hj, poissonWeight_nonneg_of_nonneg z hz j]

private lemma poissonPrefix_eq_tsum (z : ℝ) (L : ℕ) :
    (∑' j : ℕ, (if j ≤ L then poissonWeight z j else 0)) =
      ∑ j ∈ Finset.range (L + 1), poissonWeight z j := by
  rw [tsum_eq_sum (s := Finset.range (L + 1))]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjL : j ≤ L := by
      have hj' := Finset.mem_range.mp hj
      omega
    simp [hjL]
  · intro j hj
    have hj' : L + 1 ≤ j := by simpa [Finset.mem_range] using hj
    have hnot : ¬ j ≤ L := by omega
    simp [hnot]

private lemma poissonPrefix_add_tail (z : ℝ) (L : ℕ) (hz : 0 ≤ z) :
    (∑ j ∈ Finset.range (L + 1), poissonWeight z j) +
        poissonTail z ((L : ℝ) + 1) = 1 := by
  let lo : ℕ → ℝ := fun j => if j ≤ L then poissonWeight z j else 0
  let hi : ℕ → ℝ := fun j =>
    if (L : ℝ) + 1 ≤ (j : ℝ) then poissonWeight z j else 0
  have hsum : ∀ j, poissonWeight z j = lo j + hi j := by
    intro j
    by_cases hj : j ≤ L
    · have hj' : ¬ (L : ℝ) + 1 ≤ (j : ℝ) := by
        exact not_le_of_gt (by exact_mod_cast Nat.lt_succ_of_le hj)
      simp [lo, hi, hj, hj']
    · have hjlt : L < j := Nat.lt_of_not_ge hj
      have hj' : (L : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hjlt
      simp [lo, hi, hj, hj']
  have hlo : Summable lo := by
    apply (poissonWeight_summable z).of_nonneg_of_le
    · intro j
      by_cases hj : j ≤ L <;> simp [lo, hj, poissonWeight_nonneg_of_nonneg z hz j]
    · intro j
      by_cases hj : j ≤ L
      · simp [lo, hj]
      · simp [lo, hj, poissonWeight_nonneg_of_nonneg z hz j]
  have hhi : Summable hi := by
    apply (poissonWeight_summable z).of_nonneg_of_le
    · intro j
      by_cases hj : (L : ℝ) + 1 ≤ (j : ℝ) <;>
        simp [hi, hj, poissonWeight_nonneg_of_nonneg z hz j]
    · intro j
      by_cases hj : (L : ℝ) + 1 ≤ (j : ℝ)
      · simp [hi, hj]
      · simp [hi, hj, poissonWeight_nonneg_of_nonneg z hz j]
  have hlo_sum : (∑' j, lo j) = ∑ j ∈ Finset.range (L + 1), poissonWeight z j := by
    simpa [lo] using poissonPrefix_eq_tsum z L
  have hhi_sum : (∑' j, hi j) = poissonTail z ((L : ℝ) + 1) := by
    dsimp [hi]
    exact (poissonTail_eq_tsum z ((L : ℝ) + 1) hz).symm
  calc
    (∑ j ∈ Finset.range (L + 1), poissonWeight z j) +
        poissonTail z ((L : ℝ) + 1) = (∑' j, lo j) + ∑' j, hi j := by
      rw [hlo_sum, hhi_sum]
    _ = ∑' j, poissonWeight z j := by
      calc
        _ = ∑' j, (lo j + hi j) := (hlo.tsum_add hhi).symm
        _ = ∑' j, poissonWeight z j := tsum_congr (fun j => (hsum j).symm)
    _ = 1 := poissonWeight_tsum_one z

private lemma poissonTail_mono_threshold (z a b : ℝ) (hz : 0 ≤ z) (hab : a ≤ b) :
    poissonTail z b ≤ poissonTail z a := by
  rw [poissonTail_eq_tsum z b hz, poissonTail_eq_tsum z a hz]
  exact (poissonTailSeries_summable z b hz).tsum_le_tsum
    (fun j => by
      by_cases hbj : b ≤ (j : ℝ)
      · have haj : a ≤ (j : ℝ) := le_trans hab hbj
        simp [hbj, haj]
      · by_cases haj : a ≤ (j : ℝ)
        · have : (poissonWeight z j) ≥ 0 := poissonWeight_nonneg_of_nonneg z hz j
          simp [hbj, haj, this]
        · simp [hbj, haj])
    (poissonTailSeries_summable z a hz)

theorem SA_Q22aStatement_of_deps
    (h20 : ThLean.BP.SA.SA_Q20Statement)
    (hF00 : ThLean.BP.SA.SA_F00Statement)
    (hTails : PreTailsStatement)
    (hQuantile : PreQuantileStatement) :
    ThLean.BP.SA.SA_Q22aStatement := by
  intro q n hq hqn Λ η c hΛ hη hηhalf hc hcΛ hcut
  let μ : ℝ := c * ((n : ℝ) - 1)
  let L : ℕ := lowerLocation q Λ η n
  let d : ℝ := (poissonDeviation n : ℝ)
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn_gt_one : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt_one
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := hnlog.le
  have hgamma : 0 < gamma q := by
    unfold gamma
    have hqreal : 1 < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
    have hqminus : 0 < (q : ℝ) - 1 := by linarith
    have hratio : 1 < (q : ℝ) / ((q : ℝ) - 1) := by
      rw [one_lt_div hqminus]
      linarith
    exact div_pos (Real.log_pos hqreal) (Real.log_pos hratio)
  have hΛpos : 0 < Λ := by linarith
  have hμpos : 0 < μ := by
    dsimp [μ]
    apply mul_pos hc
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hμnonneg : 0 ≤ μ := hμpos.le
  have hdceil : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ d := by
    dsimp [d, poissonDeviation]
    exact Nat.le_ceil _
  have hdpos : 0 < d := by
    have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    dsimp [d]
    exact_mod_cast (lt_of_lt_of_le (mul_pos hroot hnlog) (Nat.le_ceil _))
  have hd2 : (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ d ^ 2 := by
    have hsq : (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ^ 2 =
        (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hnpos.le]
    rw [← hsq]
    nlinarith [hdceil, mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hlognonneg]
  have hquant := hQuantile q n (cap Λ n) hq hn2 η hη hηhalf
  dsimp [lowerLocation, upperLocation] at hquant
  rcases hquant with ⟨hLU, hUM, _, _, _, _, hsurvive, _⟩
  have hLcap : L ≤ cap Λ n := by
    dsimp [L]
    exact hLU.trans hUM
  have hcap : (cap Λ n : ℝ) ≤ Λ * (n : ℝ) := by
    dsimp [cap]
    exact Nat.floor_le (mul_nonneg hΛpos.le (Nat.cast_nonneg n))
  have hcut' : μ + d ≤ (L : ℝ) := by
    dsimp [μ, d, L]
    linarith [hcut]
  have hden : μ + d ≤ Λ * (n : ℝ) := by
    have hLcap' : (L : ℝ) ≤ (cap Λ n : ℝ) := by exact_mod_cast hLcap
    linarith
  have hdenpos : 0 < μ + d := by linarith
  have hfrac : (Real.log (n : ℝ)) ^ 2 / (2 * Λ) ≤ d ^ 2 / (2 * (μ + d)) := by
    have hlogsq : 0 ≤ (Real.log (n : ℝ)) ^ 2 := sq_nonneg _
    have hprod₁ := mul_le_mul_of_nonneg_left hden hlogsq
    have hprod₂ := mul_le_mul_of_nonneg_right hd2 hΛpos.le
    have hdenom₁ : 0 < 2 * Λ := by positivity
    have hdenom₂ : 0 < 2 * (μ + d) := by positivity
    apply (div_le_div_iff₀ hdenom₁ hdenom₂).2
    nlinarith [hprod₁, hprod₂]
  have herror : Real.exp (-(d ^ 2) / (2 * (μ + d))) ≤ poissonTailError Λ n := by
    dsimp [poissonTailError]
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using (neg_le_neg hfrac)
  have htailestimate : poissonTail μ (μ + d) ≤ poissonTailError Λ n := by
    exact (hTails.2.2.1 μ d hμpos hdpos).1.trans herror
  have htail : poissonTail μ ((L : ℝ) + 1) ≤ poissonTailError Λ n := by
    apply (poissonTail_mono_threshold μ (μ + d) ((L : ℝ) + 1) hμnonneg ?_).trans htailestimate
    linarith [hcut']
  have hprefix := poissonPrefix_add_tail μ L hμnonneg
  have hprefix_lower : 1 - poissonTailError Λ n ≤
      ∑ j ∈ Finset.range (L + 1), poissonWeight μ j := by
    have htaille : poissonTail μ ((L : ℝ) + 1) ≤ poissonTailError Λ n := htail
    linarith
  have h20data := h20 q n (by omega) hn2 c hc.le
  rcases h20data with ⟨hmixtureSummable, _, _, hrho⟩
  have hweight : ∀ j, 0 ≤ poissonWeight μ j := by
    intro j
    exact poissonWeight_nonneg_of_nonneg μ hμnonneg j
  have hsurvival_nonneg : ∀ j, 0 ≤ processSurvival (V := Fin n) q j := by
    intro j
    exact (hF00.2.1 q n (by omega) hn2 j).1
  have hterms : ∀ j : ℕ,
      (if j ≤ L then poissonWeight μ j * (1 - η) else 0) ≤
        poissonWeight μ j * processSurvival (V := Fin n) q j := by
    intro j
    by_cases hj : j ≤ L
    · have hs := hsurvive j (by simpa [L, lowerLocation] using hj)
      simp only [if_pos hj]
      exact mul_le_mul_of_nonneg_left (le_of_lt hs) (hweight j)
    · have hs := hsurvival_nonneg j
      simp only [if_neg hj]
      exact mul_nonneg (hweight j) hs
  have hlow_summable : Summable (fun j : ℕ =>
      if j ≤ L then poissonWeight μ j * (1 - η) else 0) := by
    apply (poissonWeight_summable μ).of_nonneg_of_le
    · intro j
      by_cases hj : j ≤ L
      · simp only [if_pos hj]
        exact mul_nonneg (hweight j) (by linarith)
      · simp [hj]
    · intro j
      by_cases hj : j ≤ L
      · simp only [if_pos hj]
        calc
          poissonWeight μ j * (1 - η) ≤ poissonWeight μ j * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) (hweight j)
          _ = poissonWeight μ j := by ring
      · simp [hj, hweight j]
  have hmixtureLower :
      (1 - η) * (∑ j ∈ Finset.range (L + 1), poissonWeight μ j) ≤
        poissonMixture μ (processSurvival (V := Fin n) q) := by
    have htsum := hlow_summable.tsum_le_tsum hterms hmixtureSummable
    have hloweq : (∑' j : ℕ,
        (if j ≤ L then poissonWeight μ j * (1 - η) else 0)) =
        (1 - η) * (∑ j ∈ Finset.range (L + 1), poissonWeight μ j) := by
      calc
        _ = ∑' j : ℕ, (if j ≤ L then poissonWeight μ j else 0) * (1 - η) := by
          apply tsum_congr
          intro j
          by_cases hj : j ≤ L <;> simp [hj]
        _ = (∑' j : ℕ, (if j ≤ L then poissonWeight μ j else 0)) * (1 - η) :=
          tsum_mul_right
        _ = (1 - η) * (∑ j ∈ Finset.range (L + 1), poissonWeight μ j) := by
          rw [poissonPrefix_eq_tsum]
          ring
    simpa [poissonMixture, hloweq] using htsum
  have hmixtureBound :
      (1 - η) * (1 - poissonTailError Λ n) ≤
        poissonMixture μ (processSurvival (V := Fin n) q) := by
    calc
      _ ≤ (1 - η) * (∑ j ∈ Finset.range (L + 1), poissonWeight μ j) := by
        apply mul_le_mul_of_nonneg_left hprefix_lower
        linarith
      _ ≤ poissonMixture μ (processSurvival (V := Fin n) q) := hmixtureLower
  have hexp : Real.exp (-Λ) ≤ Real.exp (-c) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [hrho]
  calc
    Real.exp (-Λ) * (1 - η) * (1 - poissonTailError Λ n) ≤
        Real.exp (-c) * ((1 - η) * (1 - poissonTailError Λ n)) := by
      have hfactor : 0 ≤ (1 - η) * (1 - poissonTailError Λ n) := by
        have htailerrpos : 0 < poissonTailError Λ n := by
          dsimp [poissonTailError]
          exact Real.exp_pos _
        have htailerrlt : poissonTailError Λ n < 1 := by
          dsimp [poissonTailError]
          have harg : -((Real.log (n : ℝ)) ^ 2) / (2 * Λ) < 0 := by
            exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos hnlog)) (by positivity)
          exact Real.exp_lt_one_iff.mpr harg
        have hηfac : 0 ≤ 1 - η := by linarith
        have herrfac : 0 ≤ 1 - poissonTailError Λ n := by linarith
        exact mul_nonneg hηfac herrfac
      calc
        Real.exp (-Λ) * (1 - η) * (1 - poissonTailError Λ n) =
            Real.exp (-Λ) * ((1 - η) * (1 - poissonTailError Λ n)) := by ring
        _ ≤ Real.exp (-c) * ((1 - η) * (1 - poissonTailError Λ n)) :=
          mul_le_mul_of_nonneg_right hexp hfactor
    _ ≤ Real.exp (-c) * poissonMixture μ (processSurvival (V := Fin n) q) :=
      mul_le_mul_of_nonneg_left hmixtureBound (Real.exp_nonneg _)

example (h20 : ThLean.BP.SA.SA_Q20Statement)
    (hF00 : ThLean.BP.SA.SA_F00Statement)
    (hTails : PreTailsStatement) (hQuantile : PreQuantileStatement) :
    ThLean.BP.SA.SA_Q22aStatement :=
  SA_Q22aStatement_of_deps h20 hF00 hTails hQuantile

end ThLean.W.SA41

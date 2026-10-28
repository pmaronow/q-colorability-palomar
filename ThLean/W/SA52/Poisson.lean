import ThLean.BP.SA.Alternatives

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 600000

namespace ThLean.W.SA52
open ThresholdFoundations

private lemma poissonWeight_eq_measure_singleton (μ : ℝ) (hμ : 0 ≤ μ) (j : ℕ) :
    poissonWeight μ j = (ProbabilityTheory.poissonMeasure μ.toNNReal).real {j} := by
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  have hto : (μ.toNNReal : ℝ) = μ := Real.coe_toNNReal μ hμ
  simp [poissonWeight, hto]

private lemma poissonEventMass (μ : ℝ) (hμ : 0 ≤ μ) (s : Set ℕ)
    [DecidablePred (fun j : ℕ => j ∈ s)] :
    (∑' j : ℕ, if j ∈ s then poissonWeight μ j else 0) =
      (ProbabilityTheory.poissonMeasure μ.toNNReal).real s := by
  classical
  let P := ProbabilityTheory.poissonMeasure μ.toNNReal
  calc
    (∑' j : ℕ, if j ∈ s then poissonWeight μ j else 0) =
        ∑' j : ℕ, if j ∈ s then (P {j}).toReal else 0 := by
      apply tsum_congr
      intro j
      by_cases hj : j ∈ s
      · simp [hj, P, measureReal_def, poissonWeight_eq_measure_singleton μ hμ]
      · simp [hj]
    _ = (∑' j : ℕ, if j ∈ s then P {j} else 0).toReal := by
      symm
      calc
        (∑' j : ℕ, if j ∈ s then P {j} else 0).toReal =
            ∑' j : ℕ, (if j ∈ s then P {j} else 0).toReal :=
          ENNReal.tsum_toReal_eq
            (f := fun j : ℕ => if j ∈ s then P {j} else 0)
            (fun j => by split_ifs <;> finiteness)
        _ = ∑' j : ℕ, if j ∈ s then (P {j}).toReal else 0 := by
          apply tsum_congr
          intro j
          by_cases hj : j ∈ s <;> simp [hj]
    _ = P.real s := by
      rw [measureReal_def]
      congr 1
      simpa [Set.indicator_apply] using
        (Measure.tsum_indicator_apply_singleton P s (by measurability))

private lemma poissonWeightSummable (μ : ℝ) (hμ : 0 ≤ μ) :
    Summable (poissonWeight μ) := by
  convert (ProbabilityTheory.hasSum_one_poissonMeasure μ.toNNReal).summable using 1
  funext j
  have hto : (μ.toNNReal : ℝ) = μ := Real.coe_toNNReal μ hμ
  simp [poissonWeight, hto]

lemma poissonWeight_nonneg (μ : ℝ) (hμ : 0 ≤ μ) (j : ℕ) :
    0 ≤ poissonWeight μ j := by
  rw [poissonWeight_eq_measure_singleton μ hμ]
  exact measureReal_nonneg

lemma poissonCutoffSummable (μ : ℝ) (hμ : 0 ≤ μ) (s : Set ℕ)
    [DecidablePred (fun j : ℕ => j ∈ s)]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    Summable (fun j : ℕ => poissonWeight μ j * (if j ∈ s then a else b)) := by
  classical
  apply (poissonWeightSummable μ hμ).of_nonneg_of_le
  · intro j
    have hw := poissonWeight_nonneg μ hμ j
    split_ifs <;> nlinarith [ha, hb, hw]
  · intro j
    have hw := poissonWeight_nonneg μ hμ j
    split_ifs <;> nlinarith

lemma poissonWeightedCutoff (μ : ℝ) (hμ : 0 ≤ μ) (s : Set ℕ)
    [DecidablePred (fun j : ℕ => j ∈ s)]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    (∑' j : ℕ, poissonWeight μ j * (if j ∈ s then a else b)) =
      a * (ProbabilityTheory.poissonMeasure μ.toNNReal).real s +
        b * (ProbabilityTheory.poissonMeasure μ.toNNReal).real sᶜ := by
  classical
  let P := ProbabilityTheory.poissonMeasure μ.toNNReal
  have hsumA : Summable (fun j : ℕ => a * (if j ∈ s then poissonWeight μ j else 0)) := by
    apply (poissonWeightSummable μ hμ).of_nonneg_of_le
    · intro j
      have hw := poissonWeight_nonneg μ hμ j
      split_ifs <;> nlinarith [ha, hw]
    · intro j
      have hw := poissonWeight_nonneg μ hμ j
      split_ifs <;> nlinarith
  have hsumB : Summable (fun j : ℕ => b * (if j ∈ sᶜ then poissonWeight μ j else 0)) := by
    apply (poissonWeightSummable μ hμ).of_nonneg_of_le
    · intro j
      have hw := poissonWeight_nonneg μ hμ j
      split_ifs <;> nlinarith [hb, hw]
    · intro j
      have hw := poissonWeight_nonneg μ hμ j
      split_ifs <;> nlinarith
  calc
    (∑' j : ℕ, poissonWeight μ j * (if j ∈ s then a else b)) =
        ∑' j : ℕ,
          (a * (if j ∈ s then poissonWeight μ j else 0) +
            b * (if j ∈ sᶜ then poissonWeight μ j else 0)) := by
      apply tsum_congr
      intro j
      by_cases hj : j ∈ s <;> simp [hj, Set.mem_compl_iff, mul_comm]
    _ = (∑' j : ℕ, a * (if j ∈ s then poissonWeight μ j else 0)) +
        ∑' j : ℕ, b * (if j ∈ sᶜ then poissonWeight μ j else 0) :=
      hsumA.tsum_add hsumB
    _ = a * P.real s + b * P.real sᶜ := by
      rw [tsum_mul_left, tsum_mul_left]
      have hA : (∑' j : ℕ, if j ∈ s then poissonWeight μ j else 0) = P.real s := by
        simpa [P] using poissonEventMass μ hμ s
      have hB : (∑' j : ℕ, if j ∈ sᶜ then poissonWeight μ j else 0) = P.real sᶜ := by
        simpa [P] using poissonEventMass μ hμ sᶜ
      rw [hA, hB]

lemma poissonEventMass_le_one (μ : ℝ) (_hμ : 0 ≤ μ) (s : Set ℕ) :
    (ProbabilityTheory.poissonMeasure μ.toNNReal).real s ≤ 1 := by
  let P := ProbabilityTheory.poissonMeasure μ.toNNReal
  calc
    P.real s ≤ P.real Set.univ := measureReal_mono (Set.subset_univ _) (by finiteness)
    _ = 1 := by simp [P]

lemma poissonEventMass_compl (μ : ℝ) (_hμ : 0 ≤ μ) (s : Set ℕ) :
    (ProbabilityTheory.poissonMeasure μ.toNNReal).real sᶜ =
      1 - (ProbabilityTheory.poissonMeasure μ.toNNReal).real s := by
  let P := ProbabilityTheory.poissonMeasure μ.toNNReal
  have hsum := MeasureTheory.measureReal_add_measureReal_compl
    (μ := P) (s := s) (by measurability)
  have huniv : P.real Set.univ = 1 := by simp [P]
  linarith

private lemma finiteUniformProbBounds {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) : 0 ≤ uniformProb P ∧ uniformProb P ≤ 1 := by
  classical
  unfold uniformProb uniformMean
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty A))
  constructor
  · apply div_nonneg
    · exact Finset.sum_nonneg fun x _ => by
        unfold indicator
        split_ifs <;> positivity
    · exact hcard.le
  · rw [div_le_one hcard]
    calc
      (∑ x, indicator (P x)) ≤ ∑ _x : A, (1 : ℝ) :=
        Finset.sum_le_sum fun x _ => by
          unfold indicator
          split_ifs <;> norm_num
      _ = (Fintype.card A : ℝ) := by simp

lemma processSurvivalBoundsGeneric {V : Type*} [Fintype V]
    (q m : ℕ) (hpair : ∃ u v : V, u ≠ v) :
    0 ≤ processSurvival (V := V) q m ∧ processSurvival (V := V) q m ≤ 1 := by
  obtain ⟨u, v, huv⟩ := hpair
  have hp : ∀ w : V, s(u, v) ≠ s(w, w) := by
    intro w hw
    have he := Sym2.eq_iff.mp hw
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> exact huv (h0.trans h1.symm)
  haveI : Nonempty (EdgeTuple V m) := ⟨fun _ => ⟨s(u, v), hp⟩⟩
  unfold processSurvival survival
  simp only [zero_add]
  exact finiteUniformProbBounds _

lemma processSurvivalBounds (q n m : ℕ) (hn : 2 ≤ n) :
    0 ≤ processSurvival (V := Fin n) q m ∧ processSurvival (V := Fin n) q m ≤ 1 := by
  let v₀ : Fin n := ⟨0, by omega⟩
  let v₁ : Fin n := ⟨1, by omega⟩
  have h01 : v₀ ≠ v₁ := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  exact processSurvivalBoundsGeneric q m ⟨v₀, v₁, h01⟩

private lemma poissonDeviation_bounds (n : ℕ) (hn : 6 ≤ n) :
    0 < Real.log (n : ℝ) ∧ 0 < (poissonDeviation n : ℝ) ∧
      (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ (poissonDeviation n : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hceil : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ (poissonDeviation n : ℝ) := by
    exact_mod_cast (Nat.le_ceil (Real.sqrt (n : ℝ) * Real.log (n : ℝ)))
  have hbase : 0 ≤ Real.sqrt (n : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) hlog.le
  have hdev : 0 ≤ (poissonDeviation n : ℝ) := le_trans hbase hceil
  have hsquare : (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ^ 2 =
      (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  refine ⟨hlog, lt_of_lt_of_le (mul_pos hsqrt hlog) hceil, ?_⟩
  calc
    (n : ℝ) * (Real.log (n : ℝ)) ^ 2 =
        (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ^ 2 := hsquare.symm
    _ ≤ (poissonDeviation n : ℝ) ^ 2 := (sq_le_sq₀ hbase hdev).2 hceil

private lemma poissonChebyshev (hMom : ThLean.BP.SA.SA_E01bStatement)
    (hCheb : ThLean.BP.SA.SA_X57Statement) (μ : ℝ) (hμ : 0 ≤ μ) (t : ℝ) (ht : 0 < t) :
    (∑' j : ℕ, if t ≤ |(j : ℝ) - μ| then poissonWeight μ j else 0) ≤ μ / t ^ 2 := by
  classical
  rcases hMom μ hμ with ⟨hfirst, hsquare, hmean, hfactorial, hsecond, hvariance⟩
  let P := ProbabilityTheory.poissonMeasure μ.toNNReal
  let X : ℕ → ℝ := fun j => j
  have hw (j : ℕ) : poissonWeight μ j = P.real {j} := by
    exact poissonWeight_eq_measure_singleton μ hμ j
  have hmeanInt : ∫ j, X j ∂P = μ := by
    calc
      ∫ j, X j ∂P = ∑' j : ℕ,
          (Real.exp (-(μ.toNNReal : ℝ)) * (μ.toNNReal : ℝ) ^ j /
            (Nat.factorial j : ℝ)) • X j := by
        simpa [P] using (ProbabilityTheory.integral_poissonMeasure μ.toNNReal X)
      _ = ∑' j : ℕ, poissonWeight μ j * (j : ℝ) := by
        apply tsum_congr
        intro j
        simp [X, poissonWeight, Real.coe_toNNReal μ hμ, smul_eq_mul]
      _ = μ := hmean
  have hsumSquare : Summable (fun j : ℕ => poissonWeight μ j * ‖X j ^ 2‖) := by
    have hnorm (j : ℕ) : ‖X j ^ 2‖ = (j : ℝ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (j : ℝ))]
    simpa only [hnorm] using hsquare
  have hsumSquare' : Summable
      (fun j : ℕ => (Real.exp (-(μ.toNNReal : ℝ)) *
        (μ.toNNReal : ℝ) ^ j / (Nat.factorial j : ℝ)) * ‖X j ^ 2‖) := by
    simpa [poissonWeight, Real.coe_toNNReal μ hμ] using hsumSquare
  have hIntSquare : Integrable (fun j : ℕ => X j ^ 2) P :=
    (ProbabilityTheory.integrable_poissonMeasure_iff).2 hsumSquare'
  have hMem : MemLp X 2 P :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (by simpa using hIntSquare)
  have hvarianceInt : ∫ j, (X j - μ) ^ 2 ∂P = μ := by
    calc
      ∫ j, (X j - μ) ^ 2 ∂P = ∑' j : ℕ,
          (Real.exp (-(μ.toNNReal : ℝ)) * (μ.toNNReal : ℝ) ^ j /
            (Nat.factorial j : ℝ)) • (X j - μ) ^ 2 := by
        simpa [P] using
          (ProbabilityTheory.integral_poissonMeasure μ.toNNReal (fun j : ℕ => (X j - μ) ^ 2))
      _ = ∑' j : ℕ, poissonWeight μ j * ((j : ℝ) - μ) ^ 2 := by
        apply tsum_congr
        intro j
        simp [X, poissonWeight, Real.coe_toNNReal μ hμ, smul_eq_mul]
      _ = μ := hvariance
  have hraw := hCheb ℕ P X (by fun_prop) hMem t ht
  rw [hmeanInt, hvarianceInt] at hraw
  have hmass := poissonEventMass μ hμ {j : ℕ | t ≤ |(j : ℝ) - μ|}
  rw [← hmass] at hraw
  simpa [X] using hraw

lemma poissonChebyshev_scaled_bound
    (hMom : ThLean.BP.SA.SA_E01bStatement) (hCheb : ThLean.BP.SA.SA_X57Statement)
    (n : ℕ) (hn : 6 ≤ n) (Λ c : ℝ) (hΛ : 0 < Λ) (hc : 0 < c) (hcΛ : c ≤ Λ) :
    (ProbabilityTheory.poissonMeasure (c * ((n : ℝ) - 1)).toNNReal).real
      {j : ℕ | (poissonDeviation n : ℝ) ≤
        |(j : ℝ) - c * ((n : ℝ) - 1)|} ≤
      Λ / (Real.log (n : ℝ)) ^ 2 := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hmu : 0 ≤ c * ((n : ℝ) - 1) := mul_nonneg hc.le (by linarith)
  have hmuΛ : c * ((n : ℝ) - 1) ≤ Λ * (n : ℝ) := by
    have hnsub : 0 ≤ (n : ℝ) - 1 := by linarith
    have hfirst := mul_le_mul_of_nonneg_right hcΛ hnsub
    have hsecond : Λ * ((n : ℝ) - 1) ≤ Λ * (n : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) hΛ.le
    linarith
  obtain ⟨hlog, hdevpos, hdevsq⟩ := poissonDeviation_bounds n hn
  have hlog2 : 0 < (Real.log (n : ℝ)) ^ 2 := pow_pos hlog 2
  have hdev2 : 0 < (poissonDeviation n : ℝ) ^ 2 := pow_pos hdevpos 2
  have hratio : (c * ((n : ℝ) - 1)) / (poissonDeviation n : ℝ) ^ 2 ≤
      Λ / (Real.log (n : ℝ)) ^ 2 := by
    apply (div_le_iff₀ hdev2).2
    calc
      c * ((n : ℝ) - 1) ≤ Λ * (n : ℝ) := hmuΛ
      _ ≤ (Λ / (Real.log (n : ℝ)) ^ 2) *
          (poissonDeviation n : ℝ) ^ 2 := by
        have hfrac : (n : ℝ) ≤
            (poissonDeviation n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2 :=
          (le_div_iff₀ hlog2).2 (by nlinarith [hdevsq])
        calc
          Λ * (n : ℝ) ≤ Λ * ((poissonDeviation n : ℝ) ^ 2 /
              (Real.log (n : ℝ)) ^ 2) := mul_le_mul_of_nonneg_left hfrac hΛ.le
          _ = (Λ / (Real.log (n : ℝ)) ^ 2) *
              (poissonDeviation n : ℝ) ^ 2 := by ring
  have htail := poissonChebyshev hMom hCheb (c * ((n : ℝ) - 1)) hmu
    (poissonDeviation n : ℝ) hdevpos
  have hmass := poissonEventMass (c * ((n : ℝ) - 1)) hmu
    {j : ℕ | (poissonDeviation n : ℝ) ≤
      |(j : ℝ) - c * ((n : ℝ) - 1)|}
  calc
    (ProbabilityTheory.poissonMeasure (c * ((n : ℝ) - 1)).toNNReal).real
        {j : ℕ | (poissonDeviation n : ℝ) ≤
          |(j : ℝ) - c * ((n : ℝ) - 1)|} =
        ∑' j : ℕ, if j ∈ {j : ℕ | (poissonDeviation n : ℝ) ≤
          |(j : ℝ) - c * ((n : ℝ) - 1)|} then
            poissonWeight (c * ((n : ℝ) - 1)) j else 0 := hmass.symm
    _ ≤ Λ / (Real.log (n : ℝ)) ^ 2 := by
      have htail' : (∑' j : ℕ,
          if j ∈ {j : ℕ | (poissonDeviation n : ℝ) ≤
            |(j : ℝ) - c * ((n : ℝ) - 1)|} then
              poissonWeight (c * ((n : ℝ) - 1)) j else 0) ≤
          c * ((n : ℝ) - 1) / (poissonDeviation n : ℝ) ^ 2 := by
        simpa only [Set.mem_setOf_eq] using htail
      exact htail'.trans hratio

end ThLean.W.SA52

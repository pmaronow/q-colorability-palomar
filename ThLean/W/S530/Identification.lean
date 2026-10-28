import ThLean.BP.S5.Identification

noncomputable section

namespace ThLean.W.S530

open ThLean.BP.S5
open ThresholdFoundations

private lemma identification_coefficients (q : ℕ) (hq : 3 ≤ q) :
    (q : ℝ) ≤ Real.exp (lowMeanBound q) ∧
    (q : ℝ) * Real.log (q : ℝ) ≤ Real.exp (lowMeanBound q) ∧
    (q : ℝ) ^ 2 * (Real.log (q : ℝ)) ^ 2 ≤ Real.exp (lowMeanBound q) := by
  have hq_one : 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq_one
  let x : ℝ := (q : ℝ) * Real.log (q : ℝ)
  have hx : 0 ≤ x := mul_nonneg (by positivity) hlog
  have hz : lowMeanBound q = 4 * x + 1 := by
    simp [x, lowMeanBound]
    ring
  have hqlog : (q : ℝ) - 1 ≤ x := by
    simpa [x] using Real.self_sub_one_le_mul_log (show 0 ≤ (q : ℝ) by positivity)
  have hqsmall : (q : ℝ) ≤ lowMeanBound q + 1 := by
    rw [hz]
    dsimp [x] at hqlog
    linarith
  have hxsmall : x ≤ lowMeanBound q + 1 := by
    rw [hz]
    linarith
  have hexp : lowMeanBound q + 1 ≤ Real.exp (lowMeanBound q) :=
    Real.add_one_le_exp (lowMeanBound q)
  have hmid : x ≤ lowMeanBound q / 2 + 1 := by
    rw [hz]
    linarith
  have hhalf : lowMeanBound q / 2 + 1 ≤ Real.exp (lowMeanBound q / 2) :=
    Real.add_one_le_exp (lowMeanBound q / 2)
  have hsquare : x ^ 2 ≤ Real.exp (lowMeanBound q / 2) ^ 2 :=
    (sq_le_sq₀ hx (Real.exp_nonneg _)).2 (hmid.trans hhalf)
  have hexpsquare : Real.exp (lowMeanBound q / 2) ^ 2 =
      Real.exp (lowMeanBound q) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hx2 : x ^ 2 ≤ Real.exp (lowMeanBound q) := by
    rw [← hexpsquare]
    exact hsquare
  have hx2cast : x ^ 2 = (q : ℝ) ^ 2 * (Real.log (q : ℝ)) ^ 2 := by
    dsimp [x]
    ring
  exact ⟨hqsmall.trans hexp, hxsmall.trans hexp, hx2cast ▸ hx2⟩

theorem S5_26BStatement_holds : ThLean.BP.S5.S5_26BStatement := by
  intro q N D k hq
  obtain ⟨hqcoeff, hxcoeff, hx2coeff⟩ := identification_coefficients q hq
  let z : ℝ := lowMeanBound q
  let b : ℝ := Real.exp 1 * (D : ℝ) * lowMeanBound q / (k : ℝ)
  have hqcoeff' : 2 * (q : ℝ) ≤ 2 * Real.exp z := by
    dsimp [z] at *
    nlinarith
  have hxcoeff' : 2 * ((q : ℝ) * Real.log (q : ℝ)) ≤ 2 * Real.exp z := by
    dsimp [z] at *
    nlinarith
  have hx2coeff' :
      2 * (q : ℝ) ^ 2 * (Real.log (q : ℝ)) ^ 2 ≤ 2 * Real.exp z := by
    dsimp [z] at *
    nlinarith
  have hD2 : 0 ≤ (D : ℝ) ^ 2 := sq_nonneg _
  have hDk : 0 ≤ (D : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg D) k
  have hz_nonneg : 0 ≤ lowMeanBound q := by
    have hqpos : 0 ≤ (q : ℝ) * Real.log (q : ℝ) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q)))
    unfold lowMeanBound
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have htailFactor : 0 ≤ (N : ℝ) * b ^ k :=
    mul_nonneg (Nat.cast_nonneg N) (pow_nonneg hb k)
  have htailCoeff :
      2 * ((q : ℝ) * Real.log (q : ℝ)) * ((N : ℝ) * b ^ k) ≤
        2 * Real.exp z * ((N : ℝ) * b ^ k) :=
    mul_le_mul_of_nonneg_right hxcoeff' htailFactor
  have htailCoeff' :
      2 * (q : ℝ) * Real.log (q : ℝ) * (N : ℝ) * b ^ k ≤
        2 * Real.exp z * (N : ℝ) * b ^ k := by
    convert htailCoeff using 1 <;> ring
  have hD2term :
      2 * (q : ℝ) ^ 2 * (Real.log (q : ℝ)) ^ 2 * (D : ℝ) ^ 2 ≤
        2 * Real.exp z * (D : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hx2coeff' hD2
  have hDkterm :
      2 * (Real.exp z - 1) * (D : ℝ) ^ k ≤
        2 * Real.exp z * (D : ℝ) ^ k := by
    apply mul_le_mul_of_nonneg_right _ hDk
    nlinarith [Real.exp_pos z]
  unfold rawIdentificationBound identificationBound identificationConstant lowTimeCap
  dsimp [z] at hqcoeff' hxcoeff' hx2coeff' hDkterm hD2term
  dsimp [z, b] at htailCoeff' ⊢
  calc
    2 * (q : ℝ) +
        2 * (q : ℝ) ^ 2 * (Real.log (q : ℝ)) ^ 2 * (D : ℝ) ^ 2 +
        (2 * (q : ℝ) * Real.log (q : ℝ) * (N : ℝ)) *
          (Real.exp 1 * (D : ℝ) * lowMeanBound q / (k : ℝ)) ^ k +
        2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ) ^ k
      ≤ 2 * Real.exp (lowMeanBound q) +
        2 * Real.exp (lowMeanBound q) * (D : ℝ) ^ 2 +
        2 * Real.exp (lowMeanBound q) * (N : ℝ) *
          (Real.exp 1 * (D : ℝ) * lowMeanBound q / (k : ℝ)) ^ k +
        2 * Real.exp (lowMeanBound q) * (D : ℝ) ^ k := by
          nlinarith [hqcoeff', htailCoeff', hD2term, hDkterm]
    _ = 2 * Real.exp (lowMeanBound q) *
        ((D : ℝ) ^ k + (N : ℝ) *
          (Real.exp 1 * (D : ℝ) * lowMeanBound q / (k : ℝ)) ^ k +
          (D : ℝ) ^ 2 + 1) := by ring

end ThLean.W.S530

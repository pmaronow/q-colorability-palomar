module

public import ThLean.BP.S3.Tails
public import ThLean.BP.S3.Support

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ThLean.W.S356
open ThresholdFoundations
open ThLean.BP.S3

private theorem poissonEvent_eq_poissonMeasure_real (z : ℝ) (hz : 0 ≤ z)
    (P : ℕ → Prop) :
    poissonEvent z P =
      (ProbabilityTheory.poissonMeasure (Real.toNNReal z)).real {n | P n} := by
  classical
  unfold poissonEvent
  rw [ENNReal.tsum_toReal_eq (by intro n; split_ifs <;> simp)]
  rw [measureReal_def,
    ← Measure.tsum_indicator_apply_singleton
      (μ := ProbabilityTheory.poissonMeasure (Real.toNNReal z))
      (s := {n : ℕ | P n}) (by measurability),
    ENNReal.tsum_toReal_eq (by
      intro n
      by_cases hn : P n
      · simp [hn, ProbabilityTheory.poissonMeasure_singleton]
      · simp [hn])]
  congr 1
  funext n
  by_cases hn : P n
  · simp [hn, ProbabilityTheory.poissonMeasure_singleton, poissonWeight,
      Real.coe_toNNReal z hz]
  · simp [hn]

theorem S3_49Statement_of_deps
    (h44 : ThLean.BP.S3.S3_44Statement.{0})
    (h45 : ThLean.BP.S3.S3_45Statement)
    (h46 : ThLean.BP.S3.S3_46Statement) :
    ThLean.BP.S3.S3_49Statement := by
  intro z s hz hs
  by_cases hsz : s < z
  · let x : ℝ := s / z
    let θ : ℝ := Real.log (1 - x)
    have hxpos : 0 < x := by
      dsimp [x]
      exact div_pos hs hz
    have hxlt : x < 1 := by
      dsimp [x]
      rw [div_lt_one hz]
      exact hsz
    have hbase : 0 < 1 - x := by linarith
    have hexpθ : Real.exp θ = 1 - x := by
      dsimp [θ]
      exact Real.exp_log hbase
    have hθ : θ ≤ 0 := by
      dsimp [θ]
      exact Real.log_nonpos (by linarith) (by linarith)
    let r : NNReal := Real.toNNReal z
    let μ : Measure ℕ := ProbabilityTheory.poissonMeasure r
    let X : ℕ → ℝ := fun n => (n : ℝ)
    have hXmeas : Measurable X := by
      fun_prop
    have hXint : Integrable (fun n : ℕ => Real.exp (θ * X n)) μ := by
      simpa [μ, r, X, Real.coe_toNNReal z hz.le] using (h45 r θ).1
    have hchern := (h44 (Ω := ℕ) (μ := μ) (X := X) (x := z - s) (θ := θ)
      hXmeas hXint).2 hθ
    have hmoment : (∫ n : ℕ, Real.exp (θ * (n : ℝ)) ∂μ) =
        Real.exp (z * (Real.exp θ - 1)) := by
      simpa [μ, r, Real.coe_toNNReal z hz.le] using (h45 r θ).2
    have hexp_identity :
        -θ * (z - s) + z * (Real.exp θ - 1) = -z * entropy (-x) := by
      rw [hexpθ]
      dsimp [x, θ]
      unfold entropy
      field_simp
      ring_nf
    have hent := h46.2 x (le_of_lt hxpos) hxlt
    have hquadneg : -z * (x ^ 2 / 2) = -(s ^ 2) / (2 * z) := by
      dsimp [x]
      field_simp
    have hexponent : -z * entropy (-x) ≤ -(s ^ 2) / (2 * z) := by
      calc
        -z * entropy (-x) ≤ -z * (x ^ 2 / 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hent hz.le]
        _ = -(s ^ 2) / (2 * z) := hquadneg
    have hprob := poissonEvent_eq_poissonMeasure_real z hz.le
      (fun n => (n : ℝ) ≤ z - s)
    calc
      poissonEvent z (fun n => (n : ℝ) ≤ z - s) = μ.real {n | (n : ℝ) ≤ z - s} := by
        simpa [μ] using hprob
      _ ≤ Real.exp (-θ * (z - s)) *
          (∫ n : ℕ, Real.exp (θ * (n : ℝ)) ∂μ) := hchern
      _ = Real.exp (-z * entropy (-x)) := by
        rw [hmoment, ← Real.exp_add, hexp_identity]
      _ ≤ Real.exp (-(s ^ 2) / (2 * z)) := Real.exp_le_exp.mpr hexponent
  · by_cases hsz_eq : s = z
    · subst s
      have hevent := poissonEvent_eq_poissonMeasure_real z hz.le
        (fun n => (n : ℝ) ≤ 0)
      let r : NNReal := Real.toNNReal z
      let μ : Measure ℕ := ProbabilityTheory.poissonMeasure r
      have hsubset : {n : ℕ | (n : ℝ) ≤ 0} ⊆ ({0} : Set ℕ) := by
        intro n hn
        change (n : ℝ) ≤ 0 at hn
        have hn' : n ≤ 0 := by exact_mod_cast hn
        exact Nat.eq_zero_of_le_zero hn'
      have hmass : poissonEvent z (fun n => (n : ℝ) ≤ 0) ≤ Real.exp (-z) := by
        calc
          poissonEvent z (fun n => (n : ℝ) ≤ 0) = μ.real {n | (n : ℝ) ≤ 0} := by
            simpa [μ] using hevent
          _ ≤ μ.real ({0} : Set ℕ) := MeasureTheory.measureReal_mono hsubset
          _ = Real.exp (-z) := by
            change (ProbabilityTheory.poissonMeasure r).real {0} = _
            rw [ProbabilityTheory.poissonMeasure_real_singleton]
            simp [r, Real.coe_toNNReal z hz.le]
      have hexp : Real.exp (-z) ≤ Real.exp (-(z ^ 2) / (2 * z)) := by
        apply Real.exp_le_exp.mpr
        have hz_ne : z ≠ 0 := ne_of_gt hz
        field_simp
        nlinarith
      simpa using hmass.trans hexp
    · have hzs : z < s := lt_of_le_of_ne (le_of_not_gt hsz) (Ne.symm hsz_eq)
      have hfalse : ∀ n : ℕ, ¬ (n : ℝ) ≤ z - s := by
        intro n hn
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hzero : poissonEvent z (fun n => (n : ℝ) ≤ z - s) = 0 := by
        unfold poissonEvent
        simp [hfalse]
      rw [hzero]
      positivity

end ThLean.W.S356

import ThLean.BP.S3.Tails

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.W.S354
open ThresholdFoundations
open ThLean.BP.S3

private lemma poissonEvent_eq_tsum_weight (z : ℝ) (P : ℕ → Prop)
    (hweight : ∀ n, 0 ≤ poissonWeight z n) :
    poissonEvent z P = ∑' n : ℕ, if P n then poissonWeight z n else 0 := by
  classical
  unfold poissonEvent
  rw [ENNReal.tsum_toReal_eq (fun n => by
    by_cases h : P n <;> simp [h, ENNReal.ofReal_ne_top])]
  exact tsum_congr fun n => by
    by_cases h : P n
    · simp only [if_pos h, ENNReal.toReal_ofReal (hweight n)]
    · simp only [if_neg h, ENNReal.toReal_zero]

theorem S3_47Statement_of_deps (h31 : S3_31Statement) : S3_47Statement := by
  intro z k hz hzk
  have hk : 0 < k := lt_of_le_of_lt hz hzk
  have hweight : ∀ n, 0 ≤ poissonWeight z n := (h31 z hz).1
  by_cases hz0 : z = 0
  · subst z
    rw [poissonEvent_eq_tsum_weight 0 (fun n => k ≤ (n : ℝ)) (by simpa using hweight)]
    have hzero : ∀ n : ℕ, (if k ≤ (n : ℝ) then poissonWeight 0 n else 0) = 0 := by
      intro n
      by_cases hn : n = 0
      · subst n
        simp [not_le_of_gt hk]
      · simp [poissonWeight, hn]
    have hfun : (fun n : ℕ => if k ≤ (n : ℝ) then poissonWeight 0 n else 0) = fun _ => 0 :=
      funext hzero
    rw [hfun]
    simp [Real.zero_rpow (ne_of_gt hk)]
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    let θ : ℝ := Real.log (k / z)
    have hratio : 1 < k / z := (one_lt_div hzpos).2 hzk
    have hθ : 0 < θ := Real.log_pos hratio
    have hExpθ : Real.exp θ = k / z := Real.exp_log (div_pos hk hzpos)
    rcases h31 z hz with ⟨hweight', hsum, htotal, hgen, hzero, hpos⟩
    have ha : 0 ≤ Real.exp θ := (Real.exp_pos θ).le
    rcases hgen (Real.exp θ) ha with ⟨hseries, hmoment⟩
    have hexp_nat (n : ℕ) : Real.exp (θ * (n : ℝ)) = (Real.exp θ) ^ n := by
      rw [mul_comm, Real.exp_nat_mul]
    have hseries' : Summable (fun n : ℕ => poissonWeight z n * Real.exp (θ * (n : ℝ))) := by
      simpa only [hexp_nat] using hseries
    have hmoment' : (∑' n : ℕ, poissonWeight z n * Real.exp (θ * (n : ℝ))) =
        Real.exp (z * (Real.exp θ - 1)) := by
      simpa only [hexp_nat] using hmoment
    let C : ℝ := Real.exp (-θ * k)
    let f : ℕ → ℝ := fun n => if k ≤ (n : ℝ) then poissonWeight z n else 0
    let g : ℕ → ℝ := fun n => C * (poissonWeight z n * Real.exp (θ * (n : ℝ)))
    have hterm : ∀ n, f n ≤ g n := by
      intro n
      by_cases hn : k ≤ (n : ℝ)
      · have he : Real.exp (θ * k) ≤ Real.exp (θ * (n : ℝ)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hθ.le)
        have hw := hweight' n
        simp only [f, if_pos hn, g, C]
        calc
          poissonWeight z n = 1 * poissonWeight z n := by ring
          _ = (Real.exp (-θ * k) * Real.exp (θ * k)) * poissonWeight z n := by
            have hc : Real.exp (-θ * k) * Real.exp (θ * k) = 1 := by
              rw [show -θ * k = -(θ * k) by ring, Real.exp_neg]
              exact inv_mul_cancel₀ (Real.exp_ne_zero _)
            rw [hc]
          _ ≤ (Real.exp (-θ * k) * Real.exp (θ * (n : ℝ))) * poissonWeight z n :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)) hw
          _ = Real.exp (-θ * k) * (poissonWeight z n * Real.exp (θ * (n : ℝ))) := by ring
      · dsimp [f, g, C]
        rw [if_neg hn]
        exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hweight' n) (Real.exp_nonneg _))
    have hg : Summable g := by
      dsimp [g, C]
      exact hseries'.mul_left _
    have hf : Summable f :=
      Summable.of_nonneg_of_le (fun n => by
        dsimp [f]
        split_ifs <;> simp [hweight' n]) hterm hg
    have hsumle : (∑' n : ℕ, f n) ≤ C * (∑' n : ℕ,
        poissonWeight z n * Real.exp (θ * (n : ℝ))) := by
      calc
        (∑' n : ℕ, f n) ≤ ∑' n : ℕ, g n := Summable.tsum_le_tsum hterm hf hg
        _ = C * (∑' n : ℕ, poissonWeight z n * Real.exp (θ * (n : ℝ))) := by
          dsimp [g, C]
          rw [tsum_mul_left]
    have hprob : poissonEvent z (fun n => k ≤ (n : ℝ)) ≤
        Real.exp (-θ * k + z * (Real.exp θ - 1)) := by
      rw [poissonEvent_eq_tsum_weight z (fun n => k ≤ (n : ℝ)) hweight']
      dsimp [f] at hsumle ⊢
      calc
        (∑' n : ℕ, if k ≤ (n : ℝ) then poissonWeight z n else 0) ≤
            Real.exp (-θ * k) * (∑' n : ℕ,
              poissonWeight z n * Real.exp (θ * (n : ℝ))) := hsumle
        _ = Real.exp (-θ * k) * Real.exp (z * (Real.exp θ - 1)) := by rw [hmoment']
        _ = Real.exp (-θ * k + z * (Real.exp θ - 1)) := by rw [← Real.exp_add]
    have htarget : Real.exp (-θ * k + z * (Real.exp θ - 1)) =
        Real.exp (-z) * (Real.exp 1 * z / k) ^ k := by
      dsimp [θ]
      rw [hExpθ, Real.rpow_def_of_pos (div_pos (mul_pos (Real.exp_pos 1) hzpos) hk), ← Real.exp_add]
      rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero 1) hzpos.ne') hk.ne',
        Real.log_mul (Real.exp_ne_zero 1) hzpos.ne', Real.log_exp,
        Real.log_div hk.ne' hzpos.ne']
      field_simp
      <;> ring_nf
    have hdrop : Real.exp (-z) * (Real.exp 1 * z / k) ^ k ≤
        (Real.exp 1 * z / k) ^ k := by
      have he : Real.exp (-z) ≤ 1 := by
        calc
          Real.exp (-z) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
          _ = 1 := Real.exp_zero
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right he (Real.rpow_nonneg (show 0 ≤ Real.exp 1 * z / k by positivity) k)
    exact hprob.trans (htarget ▸ hdrop)

end ThLean.W.S354

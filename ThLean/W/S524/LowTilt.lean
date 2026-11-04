module

public import ThLean.BP.S5.Identification

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S524
open ThresholdFoundations ThLean.BP.S5

private theorem poissonWeight_mul_identity (D j : ℕ) (z : ℝ) :
    poissonWeight ((D : ℝ) * z) j =
      (D : ℝ)^j * Real.exp (-((D : ℝ) - 1) * z) * poissonWeight z j := by
  unfold poissonWeight
  have he : Real.exp (-((D : ℝ) * z)) =
      Real.exp (-((D : ℝ) - 1) * z) * Real.exp (-z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, he]
  ring

theorem S5_21Statement_of_deps (hE01 : S5_E01Statement) : S5_21Statement := by
  intro D k hD z hz
  have hd0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hd1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hdz : 0 ≤ (D : ℝ) * z := mul_nonneg hd0 hz
  have hwz := hE01.1 z hz
  have hwd := hE01.1 ((D : ℝ) * z) hdz
  rcases hwz with ⟨hWz, hHasZ, hGenZ, hBoundZ⟩
  rcases hwd with ⟨hWd, hHasD, hGenD, hBoundD⟩
  constructor
  · intro j hj
    constructor
    · exact poissonWeight_mul_identity D j z
    · have hExp : Real.exp (-((D : ℝ) - 1) * z) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hd1)) hz
      have hFac : (D : ℝ)^j * Real.exp (-((D : ℝ) - 1) * z) ≤ (D : ℝ)^k := by
        calc
          (D : ℝ)^j * Real.exp (-((D : ℝ) - 1) * z) ≤
              (D : ℝ)^k * Real.exp (-((D : ℝ) - 1) * z) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hj) (Real.exp_nonneg _)
          _ ≤ (D : ℝ)^k * 1 :=
            mul_le_mul_of_nonneg_left hExp (pow_nonneg hd0 k)
          _ = (D : ℝ)^k := by ring
      rw [poissonWeight_mul_identity]
      exact mul_le_mul_of_nonneg_right hFac (hWz j).1
  · intro b hb
    rcases hBoundD 1 b (by norm_num) hb with ⟨hDb, _, _⟩
    rcases hBoundZ 1 b (by norm_num) hb with ⟨hZb, _, _⟩
    refine ⟨hDb, hZb, ?_⟩
    let f : ℕ → ℝ := fun j => poissonWeight ((D : ℝ) * z) j * b j
    let g : ℕ → ℝ := fun j => poissonWeight z j * b j
    let fLow : ℕ → ℝ := fun j => if j ≤ k then f j else 0
    let fTail : ℕ → ℝ := fun j => if k < j then f j else 0
    let wLow : ℕ → ℝ := fun j => if j ≤ k then poissonWeight ((D : ℝ) * z) j else 0
    let wTail : ℕ → ℝ := fun j => if k < j then poissonWeight ((D : ℝ) * z) j else 0
    have hFiniteLow (u : ℕ → ℝ) : Summable (fun j => if j ≤ k then u j else 0) := by
      apply summable_of_ne_finset_zero (s := Finset.range (k + 1))
      intro j hj
      have hj' : k < j := by simp only [Finset.mem_range] at hj; omega
      simp [not_le_of_gt hj']
    have hfLow : Summable fLow := by simpa [fLow] using hFiniteLow f
    have hwLow : Summable wLow := by simpa [wLow] using hFiniteLow (poissonWeight ((D : ℝ) * z))
    have hfTail : Summable fTail := by
      have hsub : Summable (fun j => f j - fLow j) := hDb.sub hfLow
      convert hsub using 1
      ext j
      by_cases hj : j ≤ k
      · simp [fLow, fTail, hj]
      · have hj' : k < j := Nat.lt_of_not_ge hj
        simp [fLow, fTail, hj, hj']
    have hwTail : Summable wTail := by
      have hsub : Summable (fun j => poissonWeight ((D : ℝ) * z) j - wLow j) := hHasD.summable.sub hwLow
      convert hsub using 1
      ext j
      by_cases hj : j ≤ k
      · simp [wLow, wTail, hj]
      · have hj' : k < j := Nat.lt_of_not_ge hj
        simp [wLow, wTail, hj, hj']
    have hsplitFun : ∀ j, f j = fLow j + fTail j := by
      intro j
      by_cases hj : j ≤ k
      · simp [fLow, fTail, hj]
      · have hj' : k < j := Nat.lt_of_not_ge hj
        simp [fLow, fTail, hj, hj']
    have hsplit : (∑' j, f j) = (∑' j, fLow j) + (∑' j, fTail j) := by
      calc
        (∑' j, f j) = ∑' j, (fLow j + fTail j) := tsum_congr fun j => hsplitFun j
        _ = (∑' j, fLow j) + (∑' j, fTail j) := Summable.tsum_add hfLow hfTail
    have hlowBound : (∑' j, fLow j) ≤ (D : ℝ)^k * poissonMixture z b := by
      have hpoint : ∀ j, fLow j ≤ (D : ℝ)^k * g j := by
        intro j
        by_cases hj : j ≤ k
        · have hwt : poissonWeight ((D : ℝ) * z) j ≤ (D : ℝ)^k * poissonWeight z j := by
            have hid := poissonWeight_mul_identity D j z
            have hExp : Real.exp (-((D : ℝ) - 1) * z) ≤ 1 := by
              apply Real.exp_le_one_iff.mpr
              exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hd1)) hz
            have hFac : (D : ℝ)^j * Real.exp (-((D : ℝ) - 1) * z) ≤ (D : ℝ)^k := by
              calc
                (D : ℝ)^j * Real.exp (-((D : ℝ) - 1) * z) ≤
                    (D : ℝ)^k * Real.exp (-((D : ℝ) - 1) * z) :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hj) (Real.exp_nonneg _)
                _ ≤ (D : ℝ)^k * 1 := mul_le_mul_of_nonneg_left hExp (pow_nonneg hd0 k)
                _ = (D : ℝ)^k := by ring
            rw [hid]
            exact mul_le_mul_of_nonneg_right hFac (hWz j).1
          calc
            fLow j = poissonWeight ((D : ℝ) * z) j * b j := by simp [fLow, f, hj]
            _ ≤ ((D : ℝ)^k * poissonWeight z j) * b j :=
              mul_le_mul_of_nonneg_right hwt (hb j).1
            _ = (D : ℝ)^k * g j := by simp [g]; ring
        · have hj' : k < j := Nat.lt_of_not_ge hj
          have hg0 : 0 ≤ g j := mul_nonneg (hWz j).1 (hb j).1
          simp only [fLow, hj, ite_false]
          exact mul_nonneg (pow_nonneg hd0 k) hg0
      calc
        (∑' j, fLow j) ≤ ∑' j, ((D : ℝ)^k * g j) := hfLow.tsum_le_tsum hpoint (hZb.mul_left ((D : ℝ)^k))
        _ = (D : ℝ)^k * poissonMixture z b := by simp [g, poissonMixture, tsum_mul_left]
    have htailBound : (∑' j, fTail j) ≤ ∑' j, wTail j := by
      apply hfTail.tsum_le_tsum
      · intro j
        by_cases hj : k < j
        · have hw0 : 0 ≤ poissonWeight ((D : ℝ) * z) j := (hWd j).1
          simpa [fTail, f, wTail, hj] using mul_le_mul_of_nonneg_left (hb j).2 hw0
        · simp [fTail, wTail, hj]
      · exact hwTail
    change (∑' j, f j) ≤ (D : ℝ)^k * poissonMixture z b + ∑' j, wTail j
    calc
      (∑' j, f j) = (∑' j, fLow j) + (∑' j, fTail j) := hsplit
      _ ≤ (D : ℝ)^k * poissonMixture z b + ∑' j, wTail j := add_le_add hlowBound htailBound
      _ = _ := by rfl

end ThLean.W.S524

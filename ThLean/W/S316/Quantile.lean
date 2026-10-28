import ThLean.BP.S3.Process
import ThLean.Defs.Sanity

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S316
open ThresholdFoundations

/-- The finite-process quantile conclusions follow from the capped distribution identities
and the finite quantile characterizations. -/
theorem S3_07bStatement_of_deps
    (h5 : ThLean.BP.S3.S3_05Statement.{u})
    (h6 : ThLean.BP.S3.S3_06bStatement.{u}) :
    ThLean.BP.S3.S3_07bStatement.{u} := by
  intro V _ q M η hq hV hη0 hηhalf
  let L := lowerQuantile (V := V) q M η
  let U := upperQuantile (V := V) q M η
  have h5' := h5 V q M hq hV
  obtain ⟨hLM, hUM, hLC, hUT, hmin, hmax, hchar⟩ :=
    h6 V q M η hV hη0 hηhalf
  have htail (m : ℕ) (hm : m ≤ M) :
      cappedTail (V := V) q M m = processSurvival (V := V) q m := h5'.2.2.1 m hm
  have hcdf (m : ℕ) (hm : m < M) :
      cappedCDF (V := V) q M m = 1 - processSurvival (V := V) q (m + 1) :=
    h5'.2.2.2.1 m hm

  have hLU : L ≤ U := by
    by_cases hL0 : L = 0
    · omega
    · have hprev : L - 1 < L := by omega
      have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
      have hprevM : L - 1 < M := lt_of_lt_of_le hprev hLM
      have hcdf_lt : cappedCDF (V := V) q M (L - 1) < η := hmin (L - 1) hprev
      have hsurv_eq : cappedCDF (V := V) q M (L - 1) =
          1 - processSurvival (V := V) q L := by
        rw [hcdf (L - 1) hprevM]
        simp [Nat.sub_add_cancel (by omega : 1 ≤ L)]
      have hsurv_strict : 1 - η < processSurvival (V := V) q L := by
        rw [hsurv_eq] at hcdf_lt
        linarith
      have hη_compl : η ≤ 1 - η := by linarith
      have htailL : η ≤ cappedTail (V := V) q M L := by
        rw [htail L hLM]
        linarith
      by_contra hnot
      have hUL : U < L := by omega
      exact (not_lt_of_ge htailL) (hmax L hUL hLM)

  have hwindow : 0 ≤ quantileWindow (V := V) q M η := by
    unfold quantileWindow
    have hcast : (L : ℝ) ≤ (U : ℝ) := Nat.cast_le.mpr hLU
    linarith

  have hlowtail : ∀ m ≤ L, 1 - η < processSurvival (V := V) q m := by
    intro m hmL
    by_cases hm0 : m = 0
    · rw [hm0, ThresholdFoundations.Sanity.processSurvival_zero
        (V := V) (by omega : 0 < q)]
      linarith
    · have hprev : m - 1 < L := by omega
      have hprevM : m - 1 < M := lt_of_lt_of_le hprev hLM
      have hcdf_lt : cappedCDF (V := V) q M (m - 1) < η := hmin (m - 1) hprev
      have hsurv_eq : cappedCDF (V := V) q M (m - 1) =
          1 - processSurvival (V := V) q m := by
        rw [hcdf (m - 1) hprevM]
        simp [Nat.sub_add_cancel (by omega : 1 ≤ m)]
      rw [hsurv_eq] at hcdf_lt
      linarith

  have hupperTail : ∀ m, U < m → m ≤ M →
      processSurvival (V := V) q m < η := by
    intro m hUm hmM
    rw [← htail m hmM]
    exact hmax m hUm hmM

  have hlevel : ∀ η' : ℝ, 0 < η' → η' ≤ η →
      lowerQuantile (V := V) q M η' ≤ L ∧
      U ≤ upperQuantile (V := V) q M η' := by
    intro η' hη'0 hη'η
    constructor
    · have hExists : ∃ m : ℕ, m ≤ M ∧
          η' ≤ cappedCDF (V := V) q M m :=
        ⟨L, hLM, le_trans hη'η hLC⟩
      unfold lowerQuantile
      rw [dif_pos hExists]
      exact Nat.find_min' hExists (m := L) ⟨hLM, le_trans hη'η hLC⟩
    · have hExists : ∃ k : ℕ, k ≤ M ∧
          η' ≤ cappedTail (V := V) q M (M - k) := by
        refine ⟨M - U, Nat.sub_le _ _, ?_⟩
        have hMU : M - (M - U) = U := Nat.sub_sub_self hUM
        simpa [hMU] using (le_trans hη'η hUT)
      unfold upperQuantile
      rw [dif_pos hExists]
      have hfind : Nat.find hExists ≤ M - U :=
        Nat.find_min' hExists (m := M - U) ⟨Nat.sub_le _ _, by
          have hMU : M - (M - U) = U := Nat.sub_sub_self hUM
          simpa [hMU] using (le_trans hη'η hUT)⟩
      omega

  exact ⟨hLU, hUM, hwindow, hlowtail, hupperTail, hlevel⟩

end ThLean.W.S316

import ThLean.BP.S3.Process

noncomputable section

open MeasureTheory

namespace ThLean.W.S313

theorem S3_06aStatement_holds : ThLean.BP.S3.S3_06aStatement := by
  intro Ω _ μ _ X M η hX hbound hη hηhalf
  dsimp only
  classical
  let L := ThLean.BP.S3.lawLower μ X M η
  let U := ThLean.BP.S3.lawUpper μ X M η
  have hmeas : MeasurableSet {ω : Ω | X ω ≤ M} := by
    exact measurableSet_le hX measurable_const
  have hmass : μ {ω : Ω | X ω ≤ M} = μ Set.univ :=
    (ae_iff_measure_eq hmeas.nullMeasurableSet).mp hbound
  have hcdfM : ThLean.BP.S3.natCDF μ X M = 1 := by
    simp [ThLean.BP.S3.natCDF, Measure.real, hmass]
  have htail0 : ThLean.BP.S3.natTail μ X 0 = 1 := by
    simp [ThLean.BP.S3.natTail]
  have hL : ∃ m : ℕ, m ≤ M ∧ η ≤ ThLean.BP.S3.natCDF μ X m := by
    exact ⟨M, le_rfl, by rw [hcdfM]; linarith⟩
  have hU : ∃ k : ℕ, k ≤ M ∧ η ≤ ThLean.BP.S3.natTail μ X (M-k) := by
    refine ⟨M, le_rfl, ?_⟩
    have hηone : η ≤ 1 := le_trans hηhalf (by norm_num)
    simpa [Nat.sub_self, htail0] using hηone
  have hLval : L = Nat.find hL := by
    simp [L, ThLean.BP.S3.lawLower, hL]
  have hUval : U = M - Nat.find hU := by
    simp [U, ThLean.BP.S3.lawUpper, hU]
  have hLspec : Nat.find hL ≤ M ∧ η ≤ ThLean.BP.S3.natCDF μ X (Nat.find hL) :=
    Nat.find_spec hL
  have hUspec : Nat.find hU ≤ M ∧
      η ≤ ThLean.BP.S3.natTail μ X (M-Nat.find hU) := Nat.find_spec hU
  have hLbound : L ≤ M := by rw [hLval]; exact hLspec.1
  have hUbound : U ≤ M := by rw [hUval]; exact Nat.sub_le _ _
  have hLcdf : η ≤ ThLean.BP.S3.natCDF μ X L := by
    rw [hLval]
    exact hLspec.2
  have hUtail : η ≤ ThLean.BP.S3.natTail μ X U := by
    rw [hUval]
    simpa [Nat.sub_sub_self hUspec.1] using hUspec.2
  refine ⟨hLbound, hUbound, hLcdf, hUtail, ?_, ?_, ?_⟩
  · intro m hm
    have hmM : m ≤ M := le_trans (Nat.le_of_lt hm) hLbound
    have hnot := Nat.find_min hL (by rw [← hLval]; exact hm)
    have hnotη : ¬ η ≤ ThLean.BP.S3.natCDF μ X m := by
      intro h
      exact hnot ⟨hmM, h⟩
    exact lt_of_not_ge hnotη
  · intro m hUm hmM
    have hUm' : M - Nat.find hU < m := by
      simpa [U, ThLean.BP.S3.lawUpper, hU] using hUm
    have hkm : M-m < Nat.find hU := by
      omega
    have hnot := Nat.find_min hU hkm
    have hnotη : ¬ η ≤ ThLean.BP.S3.natTail μ X m := by
      intro h
      apply hnot
      refine ⟨Nat.sub_le _ _, ?_⟩
      simpa [Nat.sub_sub_self hmM] using h
    exact lt_of_not_ge hnotη
  · intro m hm
    by_cases hmM : m ≤ M
    · have hfind : Nat.find hL ≤ m := Nat.find_min' hL ⟨hmM, hm⟩
      simpa [ThLean.BP.S3.lawLower, hL] using hfind
    · exact le_trans hLbound (Nat.le_of_not_ge hmM)

end ThLean.W.S313

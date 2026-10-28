import ThLean.BP.S3.Process

noncomputable section
open MeasureTheory
universe u
namespace ThLean.W.S315

/-- Paper `lem:pre-quantile`; proved from the lower quantile characterization. -/
theorem S3_07aStatement_of_deps (hdep : ThLean.BP.S3.S3_06aStatement.{u}) :
    ThLean.BP.S3.S3_07aStatement.{u} := by
  intro Ω _ μ _ X M η hX _hXM hηpos hηhalf
  let L := ThLean.BP.S3.lawLower μ X M η
  let U := ThLean.BP.S3.lawUpper μ X M η
  have hprops := hdep Ω μ X M η hX _hXM hηpos hηhalf
  change L ≤ M ∧ U ≤ M ∧ η ≤ ThLean.BP.S3.natCDF μ X L ∧
    η ≤ ThLean.BP.S3.natTail μ X U ∧
    (∀ m < L, ThLean.BP.S3.natCDF μ X m < η) ∧
    (∀ m, U < m → m ≤ M → ThLean.BP.S3.natTail μ X m < η) ∧
    (∀ m, η ≤ ThLean.BP.S3.natCDF μ X m → L ≤ m) at hprops
  rcases hprops with ⟨hL_M, hU_M, hηCDF, hηTail, hCDFstrict, hTailstrict, _⟩

  have tail_mono {m n : ℕ} (hmn : m ≤ n) :
      ThLean.BP.S3.natTail μ X n ≤ ThLean.BP.S3.natTail μ X m := by
    unfold ThLean.BP.S3.natTail
    exact measureReal_mono
      (by
        intro ω hω
        exact le_trans hmn hω)
      (by finiteness)

  have htailL : 1 - η < ThLean.BP.S3.natTail μ X L := by
    by_cases hL0 : L = 0
    · subst L
      have hzero : ThLean.BP.S3.natTail μ X 0 = 1 := by
        unfold ThLean.BP.S3.natTail
        rw [show {ω : Ω | 0 ≤ X ω} = Set.univ by ext ω; simp,
          MeasureTheory.probReal_univ]
      rw [hL0, hzero]
      linarith
    · have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
      have hstrict := hCDFstrict (L - 1) (by omega)
      have hset : {ω : Ω | L ≤ X ω} = ({ω : Ω | X ω ≤ L - 1} : Set Ω)ᶜ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
        omega
      have hmeas : MeasurableSet {ω : Ω | X ω ≤ L - 1} := by
        exact hX measurableSet_Iic
      have htail_eq : ThLean.BP.S3.natTail μ X L =
          1 - ThLean.BP.S3.natCDF μ X (L - 1) := by
        unfold ThLean.BP.S3.natTail ThLean.BP.S3.natCDF
        rw [hset, MeasureTheory.measureReal_compl hmeas,
          MeasureTheory.probReal_univ]
      rw [htail_eq]
      linarith

  have hLU : L ≤ U := by
    by_contra hnot
    have hUL : U < L := Nat.lt_of_not_ge hnot
    have hmL : U + 1 ≤ L := by omega
    have hmM : U + 1 ≤ M := hmL.trans hL_M
    have htailmono := tail_mono hmL
    have hstrict := hTailstrict (U + 1) (by omega) hmM
    have htailLower := lt_of_lt_of_le htailL htailmono
    linarith [hηhalf]

  refine ⟨htailL, hLU, ?_⟩
  intro η' hη'pos hη'le
  have hη'half : η' ≤ 1 / 2 := le_trans hη'le hηhalf
  have hprops' := hdep Ω μ X M η' hX _hXM hη'pos hη'half
  rcases hprops' with ⟨_, _, _, _, _, hTailstrict', hCDFminimal'⟩
  have hL'le : ThLean.BP.S3.lawLower μ X M η' ≤ L :=
    hCDFminimal' L (le_trans hη'le hηCDF)
  have hUle : U ≤ ThLean.BP.S3.lawUpper μ X M η' := by
    by_contra hnot
    have hlt : ThLean.BP.S3.lawUpper μ X M η' < U := Nat.lt_of_not_ge hnot
    let m := ThLean.BP.S3.lawUpper μ X M η' + 1
    have hmgt : ThLean.BP.S3.lawUpper μ X M η' < m := by dsimp [m]; omega
    have hmU : m ≤ U := by dsimp [m]; omega
    have hmM : m ≤ M := hmU.trans hU_M
    have htailmono := tail_mono hmU
    have hstrict := hTailstrict' m hmgt hmM
    have htailLower : η' ≤ ThLean.BP.S3.natTail μ X m :=
      le_trans (le_trans hη'le hηTail) htailmono
    linarith
  exact ⟨hL'le, hUle⟩

end ThLean.W.S315

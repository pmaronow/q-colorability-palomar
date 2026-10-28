import ThLean.BP.S3.Adapters

namespace ThLean.W.S393

open ThresholdFoundations

theorem S3_04cStatement_holds : ThLean.BP.S3.S3_04cStatement := by
  intro V _ hV m A
  let p : EdgeStream V → EdgeTuple V m := fun ω i => ω i.val
  change (∃ B : Set (EdgeTuple V m),
      @MeasurableSet (EdgeTuple V m) (⊤ : MeasurableSpace (EdgeTuple V m)) B ∧
        p ⁻¹' B = A) ↔
    PrefixEvent m A
  constructor
  · rintro ⟨B, _hB, hpre⟩
    intro ω ω' hagree
    have hp : p ω = p ω' := by
      funext i
      exact hagree i.val i.isLt
    rw [← hpre]
    change p ω ∈ B ↔ p ω' ∈ B
    rw [hp]
  · intro hprefix
    refine ⟨p '' A, by simp, ?_⟩
    ext ω
    constructor
    · rintro ⟨ω', hω', hp⟩
      apply (hprefix ω ω' ?_).mpr hω'
      intro i hi
      exact congrFun hp.symm ⟨i, hi⟩
    · intro hω
      exact ⟨ω, hω, rfl⟩

end ThLean.W.S393

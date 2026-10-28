import ThLean.BP.S3.Adapters

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S382

theorem S3_02cStatement_holds : ThLean.BP.S3.S3_02cStatement := by
  classical
  intro V inst hV q A G
  have hVpos : 0 < Fintype.card V := by omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hVpos
  have hVlarge : 1 < Fintype.card V := by omega
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card hVlarge a
  have hPair : Nonempty (Pair V) := by
    refine ⟨⟨s(a, b), ?_⟩⟩
    intro v hv
    have hrel := Sym2.exact hv
    rcases Sym2.rel_iff.mp hrel with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hba (hb.trans ha.symm)
    · exact hba (hb.trans ha.symm)
  have hPair_pos : 0 < Fintype.card (Pair V) := Fintype.card_pos_iff.mpr hPair
  have hden : (0 : ℝ) < (Fintype.card (Pair V) : ℝ) := Nat.cast_pos.mpr hPair_pos
  change uniformMeanENN (fun e : Pair V =>
      if FrozenPair q G e ∧ A G e then 1 else 0) =
    ENNReal.ofReal (uniformMean (fun e : Pair V =>
      indicator (FrozenPair q G e ∧ A G e)))
  unfold uniformMeanENN uniformMean indicator
  have hnum : (∑ e : Pair V, if FrozenPair q G e ∧ A G e then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (∑ e : Pair V,
        @ite ℝ (FrozenPair q G e ∧ A G e) (Classical.propDecidable _) 1 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)]
    · apply Finset.sum_congr rfl
      intro e he
      by_cases hpe : FrozenPair q G e ∧ A G e <;> simp [hpe]
    · intro e he
      by_cases hpe : FrozenPair q G e ∧ A G e <;> simp [hpe]
  rw [hnum]
  rw [show (Fintype.card (Pair V) : ℝ≥0∞) =
    ENNReal.ofReal (Fintype.card (Pair V) : ℝ) by simp]
  exact (ENNReal.ofReal_div_of_pos
    (x := ∑ e : Pair V,
      (fun e' : Pair V => @ite ℝ (FrozenPair q G e' ∧ A G e')
        (Classical.propDecidable _) 1 0) e)
    (y := (Fintype.card (Pair V) : ℝ)) hden).symm

end ThLean.W.S382

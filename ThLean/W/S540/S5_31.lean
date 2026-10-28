import ThLean.BP.S5.Occupation

noncomputable section
set_option maxHeartbeats 500000
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S540
open ThresholdFoundations ThLean.BP.S5

theorem S5_31Statement_of_deps
    (h30 : S5_30Statement)
    (hClass : PreClassmassStatement.{0})
    (hRelabel : PreRelabelStatement.{0, 0}) : S5_31Statement := by
  intro V instV q hq hV D y hy ν hν a
  let f : MGraph V → ℝ := fun G => indicator (ENNReal.ofReal y < lifetime q G)
  have hcard : 2 ≤ Fintype.card V := by omega
  have hfInv : relabelInvariant f := by
    intro π G
    have hlt := (hRelabel V V π q G).2.2.2.1
    simp [f, indicator, hlt]
  have hfBound : ∀ G, 0 ≤ f G ∧ f G ≤ 1 := by
    intro G
    simp only [f, indicator]
    split_ifs <;> norm_num
  have h30res := (h30 V q hq hcard D).2 ν hν f hfInv hfBound a
  have hLowSummable : Summable (fun G : MGraph V => (ν G).toReal * lowObservable q D y G) := by
    simpa [lowObservable, f] using h30res.1
  have hWeight : Summable (fun G : MGraph V => (ν G).toReal) := by
    simpa using (ENNReal.summable_toReal (ν.tsum_coe_ne_top))
  have hRootSummable : Summable (fun G : MGraph V =>
      (ν G).toReal * indicator (rootEvent q D a G)) := by
    refine hWeight.of_nonneg_of_le ?_ ?_
    · intro G
      exact mul_nonneg ENNReal.toReal_nonneg (by
        by_cases hr : rootEvent q D a G <;> simp [indicator, hr])
    · intro G
      by_cases hr : rootEvent q D a G <;> simp [indicator, hr] <;> positivity
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (show 1 ≤ q by omega)
  have hA : 0 ≤ lifetimeConstant q := by
    unfold lifetimeConstant
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
    positivity
  have hPartnerSummable := h30res.2.1
  have hPartnerPointwise : ∀ G : MGraph V,
      (ν G).toReal *
        (indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) * f G) ≤
      (ν G).toReal *
        ((Fintype.card V : ℝ) * Real.sqrt ((1 + lifetimeConstant q) / y) *
          indicator (rootEvent q D a G)) := by
    intro G
    have hνG : 0 ≤ (ν G).toReal := ENNReal.toReal_nonneg
    by_cases hcut : ENNReal.ofReal y < lifetime q G
    · have hf : f G = 1 := by simp [f, indicator, hcut]
      by_cases hdeg : degree G a ≤ D
      · by_cases hpart : 0 < partnerCount q G a
        · have hcolor : Colorable q G := by
            have hpos : 0 < frozenPartnerCount q G a := by
              simpa [partnerCount] using hpart
            obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
            exact (Finset.mem_filter.mp hb).2.2.1
          have hloop : Loopless G := by
            intro v
            by_contra hne
            have hpos : 0 < G (s(v, v)) := Nat.pos_of_ne_zero hne
            obtain ⟨σ, hσ⟩ := hcolor
            exact (hσ v v hpos) rfl
          have haFrozen : a ∈ frozenClass q G a := by
            simp [frozenClass, Frozen, hcolor]
          have hclassMem : frozenClass q G a ∈ frozenClasses q G := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, ?_⟩
            exact ⟨a, haFrozen⟩
          have hclass := hClass V q hq hV G hloop hcolor y hy hcut
          have hsize := hclass.2 (frozenClass q G a) hclassMem
          have hpartners : (partnerCount q G a : ℝ) ≤ (frozenClass q G a).card := by
            have hsubset :
                Finset.univ.filter (fun v => v ≠ a ∧ Frozen q G a v) ⊆ frozenClass q G a := by
              intro v hv
              simpa [frozenClass] using Finset.mem_filter.mpr
                ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2.2⟩
            have hnat := Finset.card_le_card hsubset
            have hcast :
                ((Finset.univ.filter (fun v => v ≠ a ∧ Frozen q G a v)).card : ℝ) ≤
                  ((frozenClass q G a).card : ℝ) := by exact_mod_cast hnat
            simpa [partnerCount, frozenPartnerCount] using hcast
          have hbound : (partnerCount q G a : ℝ) ≤
              (Fintype.card V : ℝ) * Real.sqrt ((1 + lifetimeConstant q) / y) := by
            exact hpartners.trans hsize
          have hroot : rootEvent q D a G := ⟨hdeg, hpart⟩
          simpa [indicator, f, hcut, hdeg, hroot, hf] using
            (mul_le_mul_of_nonneg_left hbound hνG)
        · have hrootFalse : ¬ rootEvent q D a G := by
            simp [rootEvent, hdeg, hpart]
          have hpart0 : partnerCount q G a = 0 := Nat.eq_zero_of_not_pos hpart
          simp [indicator, f, hcut, hdeg, hpart0, hrootFalse]
      · have hrootFalse : ¬ rootEvent q D a G := by
          simp [rootEvent, hdeg]
        simp [indicator, f, hcut, hdeg, hrootFalse]
    · have hf : f G = 0 := by simp [f, indicator, hcut]
      have hconst : 0 ≤ (Fintype.card V : ℝ) *
          Real.sqrt ((1 + lifetimeConstant q) / y) := by positivity
      by_cases hr : rootEvent q D a G
      · simpa [indicator, f, hcut, hr] using mul_nonneg hνG hconst
      · simp [indicator, f, hcut, hr]
  have hPartnerLe :
      lawMean ν (fun G => indicator (degree G a ≤ D) *
        (partnerCount q G a : ℝ) * f G) ≤
      ((Fintype.card V : ℝ) * Real.sqrt ((1 + lifetimeConstant q) / y)) *
        lawMean ν (fun G => indicator (rootEvent q D a G)) := by
    let C : ℝ := (Fintype.card V : ℝ) * Real.sqrt ((1 + lifetimeConstant q) / y)
    have hsumRight : Summable (fun G : MGraph V => C *
        ((ν G).toReal * indicator (rootEvent q D a G))) := hRootSummable.mul_left C
    have hpoint : ∀ G : MGraph V,
        (ν G).toReal *
          (indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) * f G) ≤
        C * ((ν G).toReal * indicator (rootEvent q D a G)) := by
      intro G
      simpa [C, mul_assoc, mul_left_comm, mul_comm] using hPartnerPointwise G
    have htsum := Summable.tsum_le_tsum hpoint hPartnerSummable hsumRight
    change (∑' G, (ν G).toReal *
        (indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) * f G)) ≤
      C * (∑' G, (ν G).toReal * indicator (rootEvent q D a G))
    calc
      _ ≤ ∑' G, C * ((ν G).toReal * indicator (rootEvent q D a G)) := htsum
      _ = C * (∑' G, (ν G).toReal * indicator (rootEvent q D a G)) := tsum_mul_left
  have hcoef : 0 ≤ 2 / ((Fintype.card V : ℝ) - 1) := by
    apply div_nonneg (by norm_num)
    have hcardR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
    linarith
  have hmain := h30res.2.2
  refine ⟨hLowSummable, hRootSummable, ?_⟩
  calc
    lawMean ν (lowObservable q D y) ≤
        (2 / ((Fintype.card V : ℝ) - 1)) *
          lawMean ν (fun G => indicator (degree G a ≤ D) *
            (partnerCount q G a : ℝ) * f G) := by
          change lawMean ν (fun G => lowKappa q D G * f G) ≤ _
          exact hmain
    _ ≤ (2 / ((Fintype.card V : ℝ) - 1)) *
          (((Fintype.card V : ℝ) * Real.sqrt ((1 + lifetimeConstant q) / y)) *
            lawMean ν (fun G => indicator (rootEvent q D a G))) :=
          mul_le_mul_of_nonneg_left hPartnerLe hcoef
    _ = (2 * Fintype.card V / ((Fintype.card V : ℝ) - 1)) *
          Real.sqrt ((1 + lifetimeConstant q) / y) *
            lawMean ν (fun G => indicator (rootEvent q D a G)) := by ring

end ThLean.W.S540

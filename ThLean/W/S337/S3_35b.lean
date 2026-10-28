import ThLean.BP.S3.Poisson

noncomputable section
open scoped BigOperators
universe u
namespace ThLean.W.S337
open ThresholdFoundations
open ThLean.BP.S3

theorem S3_35bStatement_of_deps
    (h32 : ThLean.BP.S3.S3_32Statement.{u}) :
    ThLean.BP.S3.S3_35bStatement.{u} := by
  classical
  intro E instF instN ν J label z hν hz j hcell
  obtain ⟨_, htotal, _, _⟩ := h32 E ν z hν hz
  have hzero : ∀ e, label e = j → ν e = 0 := by
    intro e hej
    have hsum : (∑ x : E, if label x = j then ν x else 0) = 0 := by
      simpa [cellMass] using hcell
    have hterms : ∀ x ∈ Finset.univ,
        0 ≤ (if label x = j then ν x else 0) := by
      intro x hx
      split
      · exact hν.1 x
      · exact le_rfl
    have hzterm :=
      (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum e (Finset.mem_univ e)
    simpa [hej] using hzterm
  have hmass_zero : ∀ w : List E, splitSublist label j w ≠ [] →
      poissonListMass z ν w = 0 := by
    intro w hw
    have hprod : (w.map ν).prod = 0 := by
      induction w with
      | nil => simp [splitSublist] at hw
      | cons e w ih =>
          by_cases hej : label e = j
          · have hνe := hzero e hej
            simp [hνe]
          · have htail : splitSublist label j w ≠ [] := by
              simpa [splitSublist, hej] using hw
            have htailProd := ih htail
            simp [htailProd]
    simp [poissonListMass, hprod]
  calc
    (∑' w : List E,
        if splitSublist label j w = [] then poissonListMass z ν w else 0) =
        ∑' w : List E, poissonListMass z ν w := by
      apply tsum_congr
      intro w
      by_cases hw : splitSublist label j w = []
      · simp [hw]
      · simp [hw, hmass_zero w hw]
    _ = 1 := htotal

end ThLean.W.S337

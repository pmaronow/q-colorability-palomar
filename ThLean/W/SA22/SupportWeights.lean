import ThLean.BP.SA.Interpolation

noncomputable section
open scoped BigOperators

namespace ThLean.W.SA22

open ThLean.BP.SA
open ThresholdFoundations

theorem SA_I11cStatement_holds : ThLean.BP.SA.SA_I11cStatement := by
  intro D instF instDec rate hrate
  have hfactor : ∀ e : D, 0 ≤ 1 - Real.exp (-rate e) := by
    intro e
    have hexp : Real.exp (-rate e) ≤ 1 :=
      (Real.exp_le_one_iff).2 (by linarith [hrate e])
    linarith
  have hweight : ∀ T : Finset D, 0 ≤ supportWeight rate T := by
    intro T
    change 0 ≤ poissonSupportWeight rate T
    simp only [poissonSupportWeight]
    apply mul_nonneg
    · exact Finset.prod_nonneg fun e he => hfactor e
    · exact Finset.prod_nonneg fun e he => (Real.exp_pos (-rate e)).le
  have hnorm :
      (∑ T ∈ (Finset.univ : Finset D).powerset, supportWeight rate T) = 1 := by
    change (∑ T ∈ (Finset.univ : Finset D).powerset,
      poissonSupportWeight rate T) = 1
    letI : DecidableEq D := fun a b => Classical.propDecidable (a = b)
    calc
      (∑ T ∈ (Finset.univ : Finset D).powerset,
          poissonSupportWeight rate T) =
          ∏ e : D, ((1 - Real.exp (-rate e)) + Real.exp (-rate e)) := by
        simpa [poissonSupportWeight, Finset.compl_eq_univ_sdiff] using
          (Fintype.prod_add
            (fun e : D => 1 - Real.exp (-rate e))
            (fun e : D => Real.exp (-rate e))).symm
      _ = 1 := by simp
  refine ⟨hweight, hnorm, ?_⟩
  intro F hF
  change 0 ≤ ∑ T ∈ (Finset.univ : Finset D).powerset,
    poissonSupportWeight rate T * F T
  exact Finset.sum_nonneg fun T hT => mul_nonneg (hweight T) (hF T)

end ThLean.W.SA22

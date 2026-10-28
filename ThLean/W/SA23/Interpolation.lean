import ThLean.BP.SA.Interpolation

noncomputable section

open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.SA

namespace ThLean.W.SA23

theorem sum_powerset_insert {D : Type} [DecidableEq D] (s : Finset D)
    (e : D) (he : e ∉ s) (f : Finset D → ℝ) :
    (∑ T ∈ (insert e s).powerset, f T) =
      ∑ U ∈ s.powerset, (f U + f (insert e U)) := by
  classical
  rw [Finset.powerset_insert]
  rw [Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [← Finset.sum_add_distrib]
    · intro A hA B hB hab
      have hAne : e ∉ A := fun hx => he (Finset.mem_powerset.mp hA hx)
      have hBne : e ∉ B := fun hx => he (Finset.mem_powerset.mp hB hx)
      have h := congrArg (fun T : Finset D => T.erase e) hab
      simpa [hAne, hBne] using h
  · apply Finset.disjoint_left.mpr
    intro T hT himg
    rcases Finset.mem_image.mp himg with ⟨U, hU, hEq⟩
    have heT : e ∈ T := by rw [← hEq]; simp
    exact he (Finset.mem_powerset.mp hT heT)

def supportDiff {D : Type} [DecidableEq D] (s t : Finset D) : Finset D :=
  @SDiff.sdiff (Finset D) (@Finset.instSDiff D (fun a b => Classical.propDecidable (a = b))) s t

noncomputable def supportOtherWeight {D : Type} [Fintype D] [DecidableEq D]
    (rate : D → ℝ) (e : D) (U : Finset D) : ℝ :=
  (∏ x ∈ U, (1 - Real.exp (-rate x))) *
    ∏ x ∈ supportDiff (Finset.univ : Finset D) (insert e U), Real.exp (-rate x)

theorem supportWeight_update_omit {D : Type} [Fintype D] [DecidableEq D]
    (rate : D → ℝ) (e : D) (U : Finset D) (t : ℝ)
    (hU : U ⊆ (Finset.univ : Finset D).erase e) :
    poissonSupportWeight (Function.update rate e t) U =
      Real.exp (-t) * supportOtherWeight rate e U := by
  have heU : e ∉ U := by
    intro hx
    exact (Finset.mem_erase.mp (hU hx)).1 rfl
  have hcomp : supportDiff (Finset.univ : Finset D) U =
      insert e (supportDiff (Finset.univ : Finset D) (insert e U)) := by
    ext x
    by_cases hxe : x = e
    · subst x
      simp [supportDiff, Finset.mem_sdiff, heU]
    · simp [supportDiff, Finset.mem_sdiff, hxe]
  have hpresent :
      (∏ x ∈ U, (1 - Real.exp (-(Function.update rate e t) x))) =
        ∏ x ∈ U, (1 - Real.exp (-rate x)) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ e := by
      intro h
      subst x
      exact heU hx
    simp [Function.update, hne]
  have hother :
      (∏ x ∈ supportDiff (Finset.univ : Finset D) (insert e U),
        Real.exp (-(Function.update rate e t) x)) =
      ∏ x ∈ supportDiff (Finset.univ : Finset D) (insert e U), Real.exp (-rate x) := by
    apply Finset.prod_congr rfl
    intro x hx
    have heOther : e ∉ supportDiff (Finset.univ : Finset D) (insert e U) := by
      simp [supportDiff, Finset.mem_sdiff]
    have hne : x ≠ e := by
      intro h
      subst x
      exact heOther hx
    simp [Function.update, hne]
  unfold poissonSupportWeight supportOtherWeight
  unfold supportDiff at *
  have hcompProd :
      (∏ x ∈ supportDiff (Finset.univ : Finset D) U,
        Real.exp (-(Function.update rate e t) x)) =
      ∏ x ∈ insert e (supportDiff (Finset.univ : Finset D) (insert e U)),
        Real.exp (-(Function.update rate e t) x) :=
    congrArg (fun s : Finset D =>
      ∏ x ∈ s, Real.exp (-(Function.update rate e t) x)) hcomp
  unfold supportDiff at hcompProd
  conv_lhs =>
    arg 2
    rw [hcompProd]
  conv_lhs =>
    arg 2
    rw [Finset.prod_insert (by simp)]
  calc
    _ = (∏ x ∈ U, (1 - Real.exp (-(Function.update rate e t) x))) *
          (Real.exp (-t) *
            ∏ x ∈ supportDiff (Finset.univ : Finset D) (insert e U),
              Real.exp (-(Function.update rate e t) x)) := by
      unfold supportDiff
      simp
    _ = Real.exp (-t) *
          ((∏ x ∈ U, (1 - Real.exp (-rate x))) *
            ∏ x ∈ supportDiff (Finset.univ : Finset D) (insert e U), Real.exp (-rate x)) := by
      unfold supportDiff
      rw [hpresent, hother]
      ring

theorem supportWeight_update_include {D : Type} [Fintype D] [DecidableEq D]
    (rate : D → ℝ) (e : D) (U : Finset D) (t : ℝ)
    (hU : U ⊆ (Finset.univ : Finset D).erase e) :
    poissonSupportWeight (Function.update rate e t) (insert e U) =
      (1 - Real.exp (-t)) * supportOtherWeight rate e U := by
  have heU : e ∉ U := by
    intro hx
    exact (Finset.mem_erase.mp (hU hx)).1 rfl
  have hpresent :
      (∏ x ∈ U, (1 - Real.exp (-(Function.update rate e t) x))) =
        ∏ x ∈ U, (1 - Real.exp (-rate x)) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ e := by
      intro h
      subst x
      exact heU hx
    simp [Function.update, hne]
  have hother :
      (∏ x ∈ supportDiff (Finset.univ : Finset D) (insert e U),
        Real.exp (-(Function.update rate e t) x)) =
      ∏ x ∈ supportDiff (Finset.univ : Finset D) (insert e U), Real.exp (-rate x) := by
    apply Finset.prod_congr rfl
    intro x hx
    have heOther : e ∉ supportDiff (Finset.univ : Finset D) (insert e U) := by
      simp [supportDiff, Finset.mem_sdiff]
    have hne : x ≠ e := by
      intro h
      subst x
      exact heOther hx
    simp [Function.update, hne]
  unfold poissonSupportWeight supportOtherWeight
  unfold supportDiff at *
  rw [Finset.prod_insert heU]
  simp only [Function.update_self]
  calc
    _ = (1 - Real.exp (-t)) * (∏ x ∈ U, (1 - Real.exp (-(Function.update rate e t) x))) *
          ∏ x ∈ supportDiff (Finset.univ : Finset D) (insert e U),
            Real.exp (-(Function.update rate e t) x) := by
      unfold supportDiff
      ring
    _ = (1 - Real.exp (-t)) *
          ((∏ x ∈ U, (1 - Real.exp (-rate x))) *
            ∏ x ∈ supportDiff (Finset.univ : Finset D) (insert e U), Real.exp (-rate x)) := by
      unfold supportDiff
      rw [hpresent, hother]
      ring


theorem supportMean_update_split {D : Type} [Fintype D] [DecidableEq D]
    (F : Finset D → ℝ) (rate : D → ℝ) (e : D) (t : ℝ) :
    supportMean F (Function.update rate e t) =
      ∑ U ∈ (Finset.univ.erase e).powerset,
        supportOtherWeight rate e U *
          (F (insert e U) + Real.exp (-t) * (F U - F (insert e U))) := by
  classical
  have hu : insert e ((Finset.univ : Finset D).erase e) = Finset.univ :=
    Finset.insert_erase (Finset.mem_univ e)
  let f : Finset D → ℝ :=
    fun T => poissonSupportWeight (Function.update rate e t) T * F T
  change (∑ T ∈ (Finset.univ : Finset D).powerset, f T) = _
  conv_lhs =>
    rw [← hu]
    rw [sum_powerset_insert (s := Finset.univ.erase e) (e := e) (he := by simp)]
  apply Finset.sum_congr rfl
  intro U hU
  have hsub : U ⊆ (Finset.univ : Finset D).erase e :=
    Finset.mem_powerset.mp hU
  dsimp [f]
  rw [supportWeight_update_omit rate e U t hsub,
    supportWeight_update_include rate e U t hsub]
  ring

theorem supportMean_increment_split {D : Type} [Fintype D] [DecidableEq D]
    (F : Finset D → ℝ) (rate : D → ℝ) (e : D) :
    supportMean (fun T => F (insert e T) - F T) rate =
      ∑ U ∈ (Finset.univ.erase e).powerset,
        supportOtherWeight rate e U *
          (Real.exp (-rate e) * (F (insert e U) - F U)) := by
  have hupdate : Function.update rate e (rate e) = rate := by
    funext x
    by_cases hxe : x = e <;> simp [Function.update, hxe]
  have hsplit := supportMean_update_split
    (fun T => F (insert e T) - F T) rate e (rate e)
  rw [hupdate] at hsplit
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro U hU
  simp

theorem SA_I12aStatement_holds : ThLean.BP.SA.SA_I12aStatement := by
  intro D hD hDec F rate e
  classical
  let P : Finset (Finset D) := (Finset.univ.erase e).powerset
  have hExp : HasDerivAt (fun t : ℝ => Real.exp (-t))
      (-Real.exp (-rate e)) (rate e) := by
    convert (Real.hasDerivAt_exp (-rate e)).comp (rate e)
      (hasDerivAt_neg (rate e)) using 1
    · funext t
      rfl
    · ring
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ U ∈ P,
        supportOtherWeight rate e U *
          (F (insert e U) + Real.exp (-t) * (F U - F (insert e U))))
      (∑ U ∈ P,
        supportOtherWeight rate e U *
          ((-Real.exp (-rate e)) * (F U - F (insert e U))))
      (rate e) := by
    apply HasDerivAt.fun_sum
    intro U hU
    have hterm := (hExp.mul_const (F U - F (insert e U))).const_add
      (F (insert e U))
    exact hterm.const_mul (supportOtherWeight rate e U)
  have hfun : (fun t : ℝ => supportMean F (Function.update rate e t)) =
      (fun t : ℝ => ∑ U ∈ P,
        supportOtherWeight rate e U *
          (F (insert e U) + Real.exp (-t) * (F U - F (insert e U)))) := by
    funext t
    exact supportMean_update_split F rate e t
  have hval : (∑ U ∈ P,
        supportOtherWeight rate e U *
          ((-Real.exp (-rate e)) * (F U - F (insert e U)))) =
      supportMean (fun T => F (insert e T) - F T) rate := by
    rw [supportMean_increment_split]
    apply Finset.sum_congr rfl
    intro U hU
    ring
  rw [hfun]
  rw [hval] at hsum
  exact hsum

end ThLean.W.SA23

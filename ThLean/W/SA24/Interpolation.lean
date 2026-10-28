import ThLean.BP.SA.Interpolation

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA24

open ThLean.BP.SA
open ThresholdFoundations

theorem SA_I12bStatement_of_deps
    (ha : SA_I12aStatement) (hd : SA_I12dStatement) : SA_I12bStatement := by
  intro D instF instD F α β
  constructor
  · let g : (D → ℝ) → ℝ := fun rates => supportMean F rates
    let c : ℝ → D → ℝ := fun t e => α e * t + β e
    have hg : ContDiff ℝ 1 g := hd D F 1
    have hc : ContDiff ℝ 1 c := by
      fun_prop
    simpa [g, c, Function.comp_def] using hg.comp hc
  · intro t
    let g : (D → ℝ) → ℝ := fun rates => supportMean F rates
    let c : ℝ → D → ℝ := fun s e => α e * s + β e
    let x : D → ℝ := c t
    let L : ℝ →L[ℝ] (D → ℝ) :=
      ContinuousLinearMap.pi (fun e => ContinuousLinearMap.toSpanSingleton ℝ (α e))
    have hcurve : HasFDerivAt c L t := by
      change HasFDerivAt (fun s : ℝ => fun e : D => α e * s + β e)
        (ContinuousLinearMap.pi (fun e => ContinuousLinearMap.toSpanSingleton ℝ (α e))) t
      rw [hasFDerivAt_pi]
      intro e
      have hm : HasDerivAt (fun s : ℝ => α e * s) (α e) t := by
        simpa using (hasDerivAt_id t).const_mul (α e)
      simpa using (hm.add_const (β e)).hasFDerivAt
    have hg : HasFDerivAt g (fderiv ℝ g x) x := by
      have hcont : ContDiff ℝ 1 g := hd D F 1
      exact (hcont.differentiable_one x).hasFDerivAt
    have hline : HasDerivAt (fun s : ℝ => g (c s))
        (fderiv ℝ g x α) t := by
      have hcomp := hg.comp t hcurve
      simpa [Function.comp_def, x, L, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.pi_apply] using hcomp.hasDerivAt
    have hpartial : ∀ e : D,
        fderiv ℝ g x (Pi.single e (1 : ℝ)) =
          supportMean (fun T => F (insert e T) - F T) x := by
      intro e
      let p : ℝ → D → ℝ := fun u => Function.update x e (x e + u)
      have hshift : HasDerivAt (fun u : ℝ => x e + u) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (x e)
      have hcoord : HasDerivAt (fun u : ℝ => g (Function.update x e (x e + u)))
          (supportMean (fun T => F (insert e T) - F T) x) 0 := by
        have hcoord' : HasDerivAt (fun s : ℝ => supportMean F (Function.update x e s))
            (supportMean (fun T => F (insert e T) - F T) x) (x e + 0) := by
          simpa using ha D F x e
        simpa [g, Function.comp_def] using hcoord'.comp 0 hshift
      have hp : HasFDerivAt p
          ((ContinuousLinearMap.pi (Pi.single e (1 : ℝ →L[ℝ] ℝ))).comp
            (ContinuousLinearMap.toSpanSingleton ℝ 1)) 0 := by
        have hu : HasFDerivAt (Function.update x e)
            (ContinuousLinearMap.pi (Pi.single e (1 : ℝ →L[ℝ] ℝ))) (x e) :=
          hasFDerivAt_update x (x e)
        have hu' : HasFDerivAt (Function.update x e)
            (ContinuousLinearMap.pi (Pi.single e (1 : ℝ →L[ℝ] ℝ))) (x e + 0) := by
          simpa using hu
        simpa [p, Function.comp_def] using hu'.comp 0 hshift.hasFDerivAt
      have hp0 : p 0 = x := by
        funext i
        by_cases hi : i = e <;> simp [p, hi]
      have hg0 : HasFDerivAt g (fderiv ℝ g (p 0)) (p 0) := by
        simpa [hp0] using hg
      have hglobal : HasDerivAt (fun u : ℝ => g (p u))
          (fderiv ℝ g x (Pi.single e (1 : ℝ))) 0 := by
        have hcomp := (hg0.comp 0 hp).hasDerivAt
        have hcomp' : HasDerivAt (fun u : ℝ => g (p u))
            (fderiv ℝ g x (fun i : D =>
              ((Pi.single e (1 : ℝ →L[ℝ] ℝ) : D → (ℝ →L[ℝ] ℝ)) i) (1 : ℝ))) 0 := by
          simpa [Function.comp_def, p, hp0, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.pi_apply] using hcomp
        have hvec : (fun i : D =>
            ((Pi.single e (1 : ℝ →L[ℝ] ℝ) : D → (ℝ →L[ℝ] ℝ)) i) (1 : ℝ)) =
            Pi.single e (1 : ℝ) := by
          funext i
          by_cases hi : i = e <;> simp [hi]
        have hglobal' := hcomp'.congr_deriv (congrArg (fderiv ℝ g x) hvec)
        simpa [p] using hglobal'
      exact hglobal.unique hcoord
    have hdecomp : α = ∑ e : D, α e • Pi.single e (1 : ℝ) := by
      funext i
      simp [Pi.single_apply]
    have hchain : fderiv ℝ g x α =
        ∑ e : D, α e * supportMean (fun T => F (insert e T) - F T) x := by
      calc
        fderiv ℝ g x α =
            fderiv ℝ g x (∑ e : D, α e • Pi.single e (1 : ℝ)) :=
          congrArg (fderiv ℝ g x) hdecomp
        _ = ∑ e : D, α e * supportMean (fun T => F (insert e T) - F T) x := by
          simp [hpartial, smul_eq_mul]
    simpa [g, c, Function.comp_def, hchain] using hline

end ThLean.W.SA24

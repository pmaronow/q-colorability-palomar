import ThLean.BP.SA.Quantiles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Filter
open scoped Topology

namespace ThLean.W.SA43

open ThLean.BP.SA

private lemma hasDerivAt_envelope {x : ℝ} (hx : 0 < x) :
    HasDerivAt envelope ((x⁻¹ * Real.sqrt x - Real.log x * (1 / (2 * Real.sqrt x))) /
      (Real.sqrt x) ^ 2) x := by
  unfold envelope
  convert (Real.hasDerivAt_log (ne_of_gt hx)).div
    (Real.hasDerivAt_sqrt (ne_of_gt hx)) (Real.sqrt_ne_zero'.2 hx) using 1

private lemma deriv_envelope {x : ℝ} (hx : 0 < x) :
    deriv envelope x = (2 - Real.log x) / (2 * x * Real.sqrt x) := by
  have h := (hasDerivAt_envelope hx).deriv
  rw [h]
  rw [Real.sq_sqrt hx.le]
  field_simp [ne_of_gt hx, Real.sqrt_ne_zero'.2 hx]
  nlinarith [Real.sq_sqrt hx.le]

private lemma envelope_nonneg_on_large {x : ℝ} (hx : Real.exp 2 ≤ x) :
    0 ≤ envelope x := by
  have hxpos : 0 < x := (Real.exp_pos 2).trans_le hx
  have hone : 1 ≤ x := by
    exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hx
  have hlog : 0 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 0) (by simpa using hone)
    simpa using h
  unfold envelope
  exact div_nonneg hlog (Real.sqrt_nonneg x)

private lemma reciprocal_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ 1 / x :=
  div_nonneg (by norm_num) hx.le

private lemma deriv_envelope_nonpos {x : ℝ} (hx : Real.exp 2 ≤ x) :
    deriv envelope x ≤ 0 := by
  have hxpos : 0 < x := (Real.exp_pos 2).trans_le hx
  have hlog : 2 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hx
    simpa using h
  rw [deriv_envelope hxpos]
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · positivity

private lemma deriv_envelope_plus_inv_nonpos {x : ℝ} (hx : Real.exp 2 ≤ x) :
    deriv (envelope + fun u : ℝ => u⁻¹) x ≤ 0 := by
  have hxpos : 0 < x := (Real.exp_pos 2).trans_le hx
  have henv := hasDerivAt_envelope hxpos
  have hinv : HasDerivAt (fun u : ℝ => u⁻¹) (-1 / x ^ 2) x :=
    (hasDerivAt_id x).inv (ne_of_gt hxpos)
  have hsum := henv.add hinv
  have hderiv : deriv (envelope + fun u : ℝ => u⁻¹) x =
      deriv envelope x + (-1 / x ^ 2) := by
    simpa only [(hasDerivAt_envelope hxpos).deriv] using hsum.deriv
  have hnonpos : deriv envelope x ≤ 0 := deriv_envelope_nonpos hx
  rw [hderiv]
  exact add_nonpos hnonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg x))

private lemma envelope_plus_inv_nonneg_on_large {x : ℝ} (hx : Real.exp 2 ≤ x) :
    0 ≤ envelope x + 1 / x := by
  exact add_nonneg (envelope_nonneg_on_large hx)
    (reciprocal_nonneg ((Real.exp_pos 2).trans_le hx))

private lemma envelope_lower_bound {x : ℝ} (hx : Real.exp 1 ≤ x) :
    1 / x ≤ envelope x := by
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlog : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    simpa using h
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hone : 1 ≤ x := by
    exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hsqrtle : Real.sqrt x ≤ x := by
    exact (Real.sqrt_le_self_iff).2 (Or.inr hone)
  have hrecip : 1 / x ≤ 1 / Real.sqrt x :=
    one_div_le_one_div_of_le hsqrtpos hsqrtle
  have hlogmul : 1 / Real.sqrt x ≤ Real.log x / Real.sqrt x :=
    div_le_div_of_nonneg_right hlog (Real.sqrt_nonneg x)
  calc
    1 / x ≤ 1 / Real.sqrt x := hrecip
    _ ≤ Real.log x / Real.sqrt x := hlogmul
    _ = envelope x := by rfl

theorem SA_Q23aStatement_holds : ThLean.BP.SA.SA_Q23aStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact ⟨envelope_nonneg_on_large hu, envelope_plus_inv_nonneg_on_large hu⟩
  · have hcont : ContinuousOn envelope (Set.Ici (Real.exp 2)) := by
      unfold envelope
      apply ContinuousOn.div
      · exact Real.continuousOn_log.mono (by
          intro x hx
          exact Set.mem_compl_singleton_iff.mpr (ne_of_gt ((Real.exp_pos 2).trans_le hx)))
      · exact Real.continuous_sqrt.continuousOn
      · intro x hx
        exact Real.sqrt_ne_zero'.2 ((Real.exp_pos 2).trans_le hx)
    have hdiff : DifferentiableOn ℝ envelope (interior (Set.Ici (Real.exp 2))) := by
      intro x hx
      have hx' : Real.exp 2 < x := by simpa using hx
      have hxpos : 0 < x := (Real.exp_pos 2).trans hx'
      exact (hasDerivAt_envelope hxpos).differentiableAt.differentiableWithinAt
    apply antitoneOn_of_deriv_nonpos (convex_Ici (Real.exp 2)) hcont hdiff
    intro x hx
    exact deriv_envelope_nonpos (le_of_lt (by simpa using hx))
  · have hcont : ContinuousOn (envelope + fun u : ℝ => u⁻¹)
        (Set.Ici (Real.exp 2)) := by
      have henv : ContinuousOn envelope (Set.Ici (Real.exp 2)) := by
        unfold envelope
        apply ContinuousOn.div
        · exact Real.continuousOn_log.mono (by
            intro x hx
            exact Set.mem_compl_singleton_iff.mpr (ne_of_gt ((Real.exp_pos 2).trans_le hx)))
        · exact Real.continuous_sqrt.continuousOn
        · intro x hx
          exact Real.sqrt_ne_zero'.2 ((Real.exp_pos 2).trans_le hx)
      have hinv : ContinuousOn (fun u : ℝ => u⁻¹) (Set.Ici (Real.exp 2)) := by
        have htmp : ContinuousOn ((fun u : ℝ => 1) / id) (Set.Ici (Real.exp 2)) := by
          apply ContinuousOn.div continuousOn_const continuousOn_id
          intro x hx
          exact ne_of_gt ((Real.exp_pos 2).trans_le hx)
        have hfun : (fun u : ℝ => u⁻¹) = ((fun u : ℝ => 1) / id) := by
          funext u
          simp
        rw [hfun]
        exact htmp
      exact henv.add hinv
    have hdiff : DifferentiableOn ℝ (envelope + fun u : ℝ => u⁻¹)
        (interior (Set.Ici (Real.exp 2))) := by
      intro x hx
      have hx' : Real.exp 2 < x := by simpa using hx
      have hxpos : 0 < x := (Real.exp_pos 2).trans hx'
      have henv : DifferentiableAt ℝ envelope x :=
        (hasDerivAt_envelope hxpos).differentiableAt
      have hinv : DifferentiableAt ℝ (fun u : ℝ => u⁻¹) x := by
        have htmp := ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x)
          (ne_of_gt hxpos)).differentiableAt
        have hfun : (fun u : ℝ => u⁻¹) = ((fun u : ℝ => 1) / id) := by
          funext u
          simp
        rw [hfun]
        exact htmp
      exact (henv.add hinv).differentiableWithinAt
    have hant : AntitoneOn (envelope + fun u : ℝ => u⁻¹) (Set.Ici (Real.exp 2)) :=
      antitoneOn_of_deriv_nonpos (convex_Ici (Real.exp 2)) hcont hdiff (by
        intro x hx
        exact deriv_envelope_plus_inv_nonpos (le_of_lt (by simpa using hx)))
    have hfun : (fun u : ℝ => envelope u + 1 / u) = envelope + (fun u : ℝ => u⁻¹) := by
      funext u
      simp
    rw [hfun]
    exact hant
  · have henv : Tendsto envelope atTop (𝓝 0) := by
      convert (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
        using 1
      funext x
      simp [envelope, Real.sqrt_eq_rpow]
    exact henv
  · have henv : Tendsto envelope atTop (𝓝 0) := by
      convert (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
        using 1
      funext x
      simp [envelope, Real.sqrt_eq_rpow]
    have hinv : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0))
    simpa using henv.add hinv
  · intro u hu
    exact envelope_lower_bound hu

end ThLean.W.SA43

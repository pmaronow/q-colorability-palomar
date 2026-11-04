module

public import ThLean.BP.S3.Tails

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
open ThresholdFoundations

namespace ThLean.W.S353

private theorem entropy_upper_tail (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 / (2 * (1 + x)) ≤ entropy x := by
  have hden : 0 < x + 2 := by linarith
  have hlog := Real.le_log_one_add_of_nonneg hx
  have hlog' := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 1 + x)
  have hfrac : x ^ 2 / (2 * (1 + x)) ≤ x ^ 2 / (x + 2) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * (1 + x)) (by positivity : 0 < x + 2)]
    nlinarith [sq_nonneg x]
  have haux : x ^ 2 / (x + 2) = (1 + x) * (2 * x / (x + 2)) - x := by
    field_simp
    ring
  calc
    x ^ 2 / (2 * (1 + x)) ≤ x ^ 2 / (x + 2) := hfrac
    _ = (1 + x) * (2 * x / (x + 2)) - x := haux
    _ ≤ (1 + x) * Real.log (1 + x) - x := by linarith
    _ = entropy x := by rfl

private theorem entropyNeg_repr (y : ℝ) :
    entropy (-y) = (1 - y) * Real.log (1 - y) + y := by
  unfold entropy
  have harg : 1 + -y = 1 - y := by ring
  rw [harg]
  ring

private def lowerTailGap (y : ℝ) : ℝ := entropy (-y) - y ^ 2 / 2

private theorem lowerTailGap_repr : lowerTailGap =
    (fun y : ℝ => (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2) := by
  funext y
  simp only [lowerTailGap, entropyNeg_repr]

private theorem lowerTailGap_deriv {y : ℝ} (hy : y < 1) :
    deriv lowerTailGap y = -Real.log (1 - y) - y := by
  have hne : 1 - y ≠ 0 := ne_of_gt (by linarith)
  rw [lowerTailGap_repr]
  change deriv (fun t : ℝ => (1 - t) * Real.log (1 - t) + t - t ^ 2 / 2) y = _
  have hfac : DifferentiableAt ℝ (fun t : ℝ => 1 - t) y := by fun_prop
  have hlog : DifferentiableAt ℝ (fun t : ℝ => Real.log (1 - t)) y := hfac.log hne
  have hmul : DifferentiableAt ℝ (fun t : ℝ => (1 - t) * Real.log (1 - t)) y := hfac.mul hlog
  have hadd : DifferentiableAt ℝ (fun t : ℝ => (1 - t) * Real.log (1 - t) + t) y :=
    hmul.add differentiableAt_id
  have hpow : DifferentiableAt ℝ (fun t : ℝ => t ^ 2 / 2) y := by fun_prop
  have hfacder : deriv (fun t : ℝ => 1 - t) y = -1 := by simp
  have hpowder : deriv (fun t : ℝ => t ^ 2 / 2) y = y := by simp
  have haddder : deriv (fun t : ℝ => (1 - t) * Real.log (1 - t) + t) y =
      deriv (fun t : ℝ => (1 - t) * Real.log (1 - t)) y + 1 := by
    simpa using deriv_fun_add hmul differentiableAt_id
  calc
    deriv (fun t : ℝ => (1 - t) * Real.log (1 - t) + t - t ^ 2 / 2) y
        = deriv (fun t : ℝ => (1 - t) * Real.log (1 - t) + t) y -
          deriv (fun t : ℝ => t ^ 2 / 2) y := deriv_fun_sub hadd hpow
    _ = deriv (fun t : ℝ => (1 - t) * Real.log (1 - t)) y + 1 -
          deriv (fun t : ℝ => t ^ 2 / 2) y := by rw [haddder]
    _ = -Real.log (1 - y) - y := by
      rw [deriv_fun_mul hfac hlog, deriv.log hfac hne, hfacder, hpowder]
      field_simp
      ring

private theorem entropy_lower_tail (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    x ^ 2 / 2 ≤ entropy (-x) := by
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) x) := convex_Icc _ _
  have hcont : ContinuousOn lowerTailGap (Set.Icc (0 : ℝ) x) := by
    intro y hy
    rw [lowerTailGap_repr]
    have hpos : 0 < 1 - y := by linarith [lt_of_le_of_lt hy.2 hx1]
    have hfac : ContinuousAt (fun t : ℝ => 1 - t) y := continuousAt_const.sub continuousAt_id
    have hlog : ContinuousAt (fun t : ℝ => Real.log (1 - t)) y :=
      (Real.continuousAt_log hpos.ne').comp hfac
    have hmul : ContinuousAt (fun t : ℝ => (1 - t) * Real.log (1 - t)) y := hfac.mul hlog
    have hadd : ContinuousAt (fun t : ℝ => (1 - t) * Real.log (1 - t) + t) y :=
      hmul.add continuousAt_id
    have hpow : ContinuousAt (fun t : ℝ => t ^ 2 / 2) y := by fun_prop
    exact hadd.continuousWithinAt.sub hpow.continuousWithinAt
  have hdiff : DifferentiableOn ℝ lowerTailGap (interior (Set.Icc (0 : ℝ) x)) := by
    intro y hy
    rw [lowerTailGap_repr]
    have hy' : y ∈ Set.Icc (0 : ℝ) x := interior_subset hy
    have hpos : 0 < 1 - y := by linarith [lt_of_le_of_lt hy'.2 hx1]
    have hfac : DifferentiableAt ℝ (fun t : ℝ => 1 - t) y := by fun_prop
    have hlog : DifferentiableAt ℝ (fun t : ℝ => Real.log (1 - t)) y := hfac.log hpos.ne'
    have hmul : DifferentiableAt ℝ (fun t : ℝ => (1 - t) * Real.log (1 - t)) y := hfac.mul hlog
    have hadd : DifferentiableAt ℝ (fun t : ℝ => (1 - t) * Real.log (1 - t) + t) y :=
      hmul.add differentiableAt_id
    have hpow : DifferentiableAt ℝ (fun t : ℝ => t ^ 2 / 2) y := by fun_prop
    exact (hadd.sub hpow).differentiableWithinAt
  have hmono : MonotoneOn lowerTailGap (Set.Icc (0 : ℝ) x) := by
    apply monotoneOn_of_deriv_nonneg hconv hcont hdiff
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) x := interior_subset hy
    have hy1 : y < 1 := lt_of_le_of_lt hy'.2 hx1
    rw [lowerTailGap_deriv hy1]
    have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - y)
    linarith
  have hzero : lowerTailGap 0 = 0 := by simp [lowerTailGap, entropy]
  have hle := hmono (a := 0) (b := x) ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  rw [hzero] at hle
  change 0 ≤ entropy (-x) - x ^ 2 / 2 at hle
  linarith

theorem S3_46Statement_holds : ThLean.BP.S3.S3_46Statement := by
  constructor
  · exact entropy_upper_tail
  · exact entropy_lower_tail

end ThLean.W.S353

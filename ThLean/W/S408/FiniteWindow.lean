import ThLean.BP.S4.Finite

noncomputable section
open scoped BigOperators
namespace ThLean.W.S408
open ThresholdFoundations

private theorem uniformMean_mono {A : Type} [Fintype A] [Nonempty A]
    {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  have hsum : (∑ x : A, f x) ≤ ∑ x : A, g x :=
    Finset.sum_le_sum (fun x _ => h x)
  have hcard : (0 : ℝ) < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›)
  exact div_le_div_of_nonneg_right hsum (le_of_lt hcard)

private theorem uniformMean_mul_const {A : Type} [Fintype A]
    (c : ℝ) (f : A → ℝ) : uniformMean (fun x => c * f x) = c * uniformMean f := by
  unfold uniformMean
  change (∑ x : A, c * f x) / (Fintype.card A : ℝ) =
    c * ((∑ x : A, f x) / (Fintype.card A : ℝ))
  rw [← Finset.mul_sum]
  ring

private theorem min_rescale {a w y : ℝ} (ha : 0 < a) (haw : a ≤ w)
    (hy : 0 ≤ y) : min w y ≤ (w / a) * min a y := by
  by_cases hya : y ≤ a
  · have hyw : y ≤ w := le_trans hya haw
    rw [min_eq_right hyw, min_eq_right hya]
    have hdiv : a / a ≤ w / a :=
      div_le_div_of_nonneg_right haw (le_of_lt ha)
    have hratio : (1 : ℝ) ≤ w / a := by
      simpa [ha.ne'] using hdiv
    calc
      y = 1 * y := by ring
      _ ≤ (w / a) * y := mul_le_mul_of_nonneg_right hratio hy
  · have hay : a ≤ y := le_of_not_ge hya
    rw [min_eq_left hay]
    calc
      min w y ≤ w := min_le_left _ _
      _ = (w / a) * a := by field_simp [ha.ne']

theorem S4_ALG_02AStatement_holds : ThLean.BP.S4.S4_ALG_02AStatement := by
  classical
  intro A instF instNE R P η a U w B hR hη ha hU hw hB hscale hcap
  by_cases hwa : w ≤ a
  · exact le_trans hwa (le_max_left _ _)
  · have haw : a ≤ w := le_of_lt (lt_of_not_ge hwa)
    have hwpos : 0 < w := lt_of_lt_of_le ha haw
    have hmean :
        uniformMean (fun x => if P x then min w (R x) else 0) ≤
          (w / a) * uniformMean (fun x => if P x then min a (R x) else 0) := by
      calc
        uniformMean (fun x => if P x then min w (R x) else 0) ≤
            uniformMean (fun x => (w / a) * (if P x then min a (R x) else 0)) := by
          apply uniformMean_mono
          intro x
          by_cases hp : P x
          · simpa [hp] using min_rescale ha haw (hR x)
          · simp [hp]
        _ = (w / a) * uniformMean (fun x => if P x then min a (R x) else 0) :=
          uniformMean_mul_const _ _
    have hratio_nonneg : 0 ≤ w / a := by positivity
    have hmeanB :
        uniformMean (fun x => if P x then min w (R x) else 0) ≤ (w / a) * B := by
      calc
        uniformMean (fun x => if P x then min w (R x) else 0) ≤
            (w / a) * uniformMean (fun x => if P x then min a (R x) else 0) := hmean
        _ ≤ (w / a) * B := mul_le_mul_of_nonneg_left hcap hratio_nonneg
    have hbound : η ^ 2 * w ^ 2 ≤ 2 * U * ((w / a) * B) := by
      calc
        η ^ 2 * w ^ 2 ≤
            2 * U * uniformMean (fun x => if P x then min w (R x) else 0) := hscale
        _ ≤ 2 * U * ((w / a) * B) :=
          mul_le_mul_of_nonneg_left hmeanB (by positivity)
    have hmul : (η ^ 2 * w * a) * w ≤ (2 * U * B) * w := by
      calc
        (η ^ 2 * w * a) * w = η ^ 2 * w ^ 2 * a := by ring
        _ ≤ (2 * U * ((w / a) * B)) * a :=
          mul_le_mul_of_nonneg_right hbound (le_of_lt ha)
        _ = (2 * U * B) * w := by field_simp [ha.ne']
    have hcancel : η ^ 2 * w * a ≤ 2 * U * B :=
      (mul_le_mul_iff_of_pos_right hwpos).mp hmul
    have hden : 0 < η ^ 2 * a := mul_pos (sq_pos_of_pos hη) ha
    have hwle : w ≤ 2 * U * B / (η ^ 2 * a) := by
      apply (le_div_iff₀ hden).2
      nlinarith [hcancel]
    exact le_max_of_le_right hwle

example : ThLean.BP.S4.S4_ALG_02AStatement := S4_ALG_02AStatement_holds

end ThLean.W.S408

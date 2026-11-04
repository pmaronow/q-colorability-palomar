module

public import ThLean.BP.S5.Identification

@[expose] public section

noncomputable section
open scoped BigOperators Topology

namespace ThLean.W.S523S
open ThresholdFoundations ThLean.BP.S5

theorem weight_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ poissonWeight r n := by
  unfold poissonWeight
  positivity

theorem weight_hasSum (r : ℝ) : HasSum (poissonWeight r) 1 := by
  convert (NormedSpace.expSeries_div_hasSum_exp r).mul_left (Real.exp (-r)) using 1
  · funext n
    simp [poissonWeight, mul_div_assoc]
  · simp [← Real.exp_eq_exp_ℝ, ← Real.exp_add]

def mass {I : Type} [Fintype I] (r : I → ℝ) (x : I → ℕ) : ℝ :=
  ∏ i, poissonWeight (r i) (x i)

def mean {I : Type} [Fintype I] (r : I → ℝ) (f : (I → ℕ) → ℝ) : ℝ :=
  ∑' x, mass r x * f x

theorem countMean_eq_mean {V : Type} [Fintype V] (r : ℝ) (f : MGraph V → ℝ) :
    countMean r f = mean (perPairRate r) f := by
  unfold countMean independentPoissonGraphMean independentPoissonGraphMass mean mass
  rfl

theorem mass_nonneg {I : Type} [Fintype I] {r : I → ℝ} (hr : ∀ i, 0 ≤ r i)
    (x : I → ℕ) : 0 ≤ mass r x :=
  Finset.prod_nonneg (fun i _ => weight_nonneg (hr i) _)

theorem mass_hasSum (I : Type) [Fintype I] (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) :
    HasSum (mass r) 1 := by
  classical
  revert r hr
  refine Fintype.induction_empty_option (P := fun I _ =>
    ∀ r : I → ℝ, (∀ i, 0 ≤ r i) → HasSum (mass r) 1) ?_ ?_ ?_ I
  · intro A B _ e ih r hr
    let : Fintype A := Fintype.ofEquiv B e.symm
    let E : (B → ℕ) ≃ (A → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have h := ih (r ∘ e) (fun a => hr (e a))
    apply E.symm.hasSum_iff.mp
    convert h using 1
    funext x
    simpa [mass, E, Equiv.arrowCongr, Function.comp_def] using
      (e.prod_comp (fun b => poissonWeight (r b) (x (e.symm b)))).symm
  · intro r hr
    simpa [mass] using (hasSum_fintype (mass r))
  · intro A _ ih r hr
    have h := ih (fun a => r (some a)) (fun a => hr (some a))
    have hn := weight_hasSum (r none)
    have hs := hn.summable.mul_of_nonneg h.summable
      (fun n => weight_nonneg (hr none) n) (mass_nonneg (fun a => hr (some a)))
    have hp := hn.mul h hs
    change HasSum (fun x => mass r x) 1
    simpa [Function.comp_def, mass, Fintype.prod_option] using
      (Equiv.piOptionEquivProd (β := fun _ : Option A => ℕ)).hasSum_iff.mpr hp

theorem mean_summable {I : Type} [Fintype I] {r : I → ℝ} (hr : ∀ i, 0 ≤ r i)
    {f : (I → ℕ) → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    Summable (fun x => mass r x * f x) := by
  apply Summable.of_norm_bounded ((mass_hasSum I r hr).summable.mul_left C)
  intro x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mass_nonneg hr x)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (hf x) (mass_nonneg hr x)

theorem mean_const {I : Type} [Fintype I] {r : I → ℝ} (hr : ∀ i, 0 ≤ r i)
    (C : ℝ) : mean r (fun _ => C) = C := by
  change (∑' x, mass r x * C) = C
  simpa using ((mass_hasSum I r hr).mul_right C).tsum_eq

theorem mean_nonneg {I : Type} [Fintype I] {r : I → ℝ} (hr : ∀ i, 0 ≤ r i)
    {f : (I → ℕ) → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean r f :=
  tsum_nonneg (fun x => mul_nonneg (mass_nonneg hr x) (hf x))

theorem mean_mono {I : Type} [Fintype I] {r : I → ℝ} (hr : ∀ i, 0 ≤ r i)
    {f g : (I → ℕ) → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C)
    (hg : ∃ C, ∀ x, |g x| ≤ C) (hfg : ∀ x, f x ≤ g x) : mean r f ≤ mean r g :=
  (mean_summable hr hf.choose_spec).tsum_le_tsum
    (fun x => mul_le_mul_of_nonneg_left (hfg x) (mass_nonneg hr x))
    (mean_summable hr hg.choose_spec)

theorem mean_abs_le {I : Type} [Fintype I] {r : I → ℝ} (hr : ∀ i, 0 ≤ r i)
    {f : (I → ℕ) → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) : |mean r f| ≤ C := by
  apply abs_le.mpr
  constructor
  · simpa [mean_const hr] using mean_mono hr
      ⟨|-C|, fun _ => le_rfl⟩ ⟨C, hf⟩ (fun x => (abs_le.mp (hf x)).1)
  · simpa [mean_const hr] using mean_mono hr
      ⟨C, hf⟩ ⟨|C|, fun _ => le_rfl⟩ (fun x => (abs_le.mp (hf x)).2)

theorem mean_add {I : Type} [Fintype I] {r : I → ℝ} (hr : ∀ i, 0 ≤ r i)
    {f g : (I → ℕ) → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C)
    (hg : ∃ C, ∀ x, |g x| ≤ C) :
    mean r (fun x => f x + g x) = mean r f + mean r g := by
  unfold mean
  simp_rw [mul_add]
  exact (mean_summable hr hf.choose_spec).tsum_add
    (mean_summable hr hg.choose_spec)

theorem weighted_comm {A B : Type} (w : A → ℝ) (v : B → ℝ)
    (hw : Summable w) (hv : Summable v) (hw0 : ∀ a, 0 ≤ w a) (hv0 : ∀ b, 0 ≤ v b)
    (f : A → B → ℝ) (hf : ∃ C, ∀ a b, |f a b| ≤ C) :
    (∑' a, w a * ∑' b, v b * f a b) = ∑' b, v b * ∑' a, w a * f a b := by
  obtain ⟨C, hC⟩ := hf
  have hs : Summable (fun p : A × B => w p.1 * v p.2 * f p.1 p.2) := by
    apply Summable.of_norm_bounded ((hw.mul_of_nonneg hv hw0 hv0).mul_right C)
    intro p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hw0 _) (hv0 _))]
    exact mul_le_mul_of_nonneg_left (hC _ _) (mul_nonneg (hw0 _) (hv0 _))
  calc
    _ = ∑' a, ∑' b, w a * v b * f a b := by
      apply tsum_congr
      intro a
      rw [← tsum_mul_left]
      apply tsum_congr
      intro b
      ring
    _ = ∑' b, ∑' a, w a * v b * f a b :=
      (Summable.tsum_comm (f := fun a b => w a * v b * f a b) hs).symm
    _ = _ := by
      apply tsum_congr
      intro b
      rw [← tsum_mul_left]
      apply tsum_congr
      intro a
      ring

theorem mean_indicator_nonzero {I : Type} [Fintype I] {r : I → ℝ}
    (hr : ∀ i, 0 ≤ r i) :
    mean r (fun x => indicator (x ≠ 0)) = 1 - mass r 0 := by
  classical
  have he (x : I → ℕ) : mass r x * indicator (x ≠ 0) =
      mass r x - if x = 0 then mass r 0 else 0 := by
    by_cases h : x = 0 <;> simp [indicator, h]
  unfold mean
  simp_rw [he]
  rw [((mass_hasSum I r hr).summable).tsum_sub (hasSum_ite_eq 0 (mass r 0)).summable]
  simp [(mass_hasSum I r hr).tsum_eq]

theorem mean_indicator_nonzero_le {I : Type} [Fintype I] {r : I → ℝ}
    (hr : ∀ i, 0 ≤ r i) : mean r (fun x => indicator (x ≠ 0)) ≤ ∑ i, r i := by
  classical
  rw [mean_indicator_nonzero hr]
  have hm : mass r 0 = Real.exp (-(∑ i, r i)) := by
    simp [mass, poissonWeight, ← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hm]
  linarith [Real.add_one_le_exp (-(∑ i, r i))]

theorem perPairRate_nonneg {V : Type} {r : ℝ} (hr : 0 ≤ r) (e : Sym2 V) :
    0 ≤ perPairRate r e := by
  classical
  unfold perPairRate
  split_ifs <;> positivity

theorem sum_perPairRate {V : Type} [Fintype V] (r : ℝ) :
    (∑ e : Sym2 V, perPairRate r e) = ((Fintype.card V).choose 2 : ℝ) * r := by
  classical
  have hd (e : Sym2 V) : (∃ v, e = s(v, v)) ↔ e.IsDiag := by
    induction e using Sym2.ind with | h a b => simp [eq_comm]
  have he : (∑ e : Sym2 V, perPairRate r e) =
      ∑ e : {e : Sym2 V // ¬e.IsDiag}, r := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun e : Sym2 V => ¬e.IsDiag))
      (by simp) (fun _ => r)]
    simp only [perPairRate, hd, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : e.IsDiag <;> simp [h]
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Sym2.card_subtype_not_diag]

theorem countMean_nonzero_le {V : Type} [Fintype V] {r : ℝ} (hr : 0 ≤ r) :
    countMean r (fun R : MGraph V => indicator (R ≠ 0)) ≤
      ((Fintype.card V).choose 2 : ℝ) * r := by
  change mean (perPairRate r) _ ≤ _
  exact (mean_indicator_nonzero_le (perPairRate_nonneg hr)).trans_eq (sum_perPairRate r)

end ThLean.W.S523S

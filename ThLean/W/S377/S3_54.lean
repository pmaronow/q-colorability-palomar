import ThLean.BP.S3.Centre

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S377
open ThresholdFoundations ThLean.BP.S3
universe u

private theorem uniformMeanENN_indicator {A : Type*} [Fintype A] (P : A → Prop) :
    uniformMeanENN (fun a => if P a then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (uniformProb P) := by
  by_cases hc : Fintype.card A = 0
  · have hEmpty : IsEmpty A := Fintype.card_eq_zero_iff.mp hc
    letI := hEmpty
    simp [uniformMeanENN, uniformProb, uniformMean]
  · have hp : 0 < (Fintype.card A : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    rw [uniformMeanENN, uniformProb, uniformMean]
    rw [ENNReal.ofReal_div_of_pos hp]
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by
      simp [indicator]
      split_ifs <;> norm_num)]
    simp only [ENNReal.ofReal_natCast]
    apply congrArg (fun z : ℝ≥0∞ => z / (Fintype.card A : ℝ≥0∞))
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hPa : P a <;> simp [indicator, hPa]

private theorem survival_nonneg_aux {V : Type*} [Fintype V] (q k : ℕ) :
    0 ≤ survival (V := V) q (0 : MGraph V) k := by
  unfold survival uniformProb uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => by
      simp [indicator]
      split_ifs <;> norm_num
  · positivity

private theorem survival_le_one_aux {V : Type*} [Fintype V] (q k : ℕ) :
    survival (V := V) q (0 : MGraph V) k ≤ 1 := by
  unfold survival uniformProb uniformMean
  by_cases hc : Fintype.card (EdgeTuple V k) = 0
  · have hEmpty : IsEmpty (EdgeTuple V k) := Fintype.card_eq_zero_iff.mp hc
    letI := hEmpty
    simp
  · have hp : 0 < (Fintype.card (EdgeTuple V k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    rw [div_le_iff₀ hp]
    calc
      ∑ x, indicator (Colorable q ((0 : MGraph V) + tupleGraph x)) ≤
          ∑ _x : EdgeTuple V k, (1 : ℝ) :=
        Finset.sum_le_sum fun x _ => by
          simp [indicator]
          split_ifs <;> norm_num
      _ = (Fintype.card (EdgeTuple V k) : ℝ) := by simp
      _ = 1 * (Fintype.card (EdgeTuple V k) : ℝ) := by ring

private theorem poissonGraphMeanENN_eq_ofReal
    {V : Type*} [Fintype V] (q : ℕ) (h31 : S3_31Statement)
    (t : ℝ) (ht : 0 ≤ t) :
    poissonGraphMeanENN t (fun G : MGraph V =>
      if Colorable q G then (1 : ℝ≥0∞) else 0) =
        ENNReal.ofReal (poissonGraphMean t
          (fun G : MGraph V => indicator (Colorable q G))) := by
  let s : ℕ → ℝ := fun k => survival q (0 : MGraph V) k
  let w : ℕ → ℝ := fun k => poissonWeight t k
  have hs0 (k : ℕ) : 0 ≤ s k := survival_nonneg_aux q k
  have hs1 (k : ℕ) : s k ≤ 1 := survival_le_one_aux q k
  have hw (k : ℕ) : 0 ≤ w k := (h31 t ht).1 k
  have hweights : Summable w := by simpa [w] using (h31 t ht).2.1
  have hterms : Summable (fun k => w k * s k) := by
    apply Summable.of_nonneg_of_le (f := w) (g := fun k => w k * s k)
    · intro k
      exact mul_nonneg (hw k) (hs0 k)
    · intro k
      calc
        w k * s k ≤ w k * 1 := mul_le_mul_of_nonneg_left (hs1 k) (hw k)
        _ = w k := by ring
    · exact hweights
  have hrmean : poissonGraphMean t (fun G : MGraph V => indicator (Colorable q G)) =
      ∑' k, w k * s k := by
    simp [poissonGraphMean, poissonMixture, survival,
      uniformProb, uniformMean, indicator, w, s]
  have hmeanENN (k : ℕ) :
      uniformMeanENN (fun x : EdgeTuple V k =>
        if Colorable q (tupleGraph x) then (1 : ℝ≥0∞) else 0) =
        ENNReal.ofReal (s k) := by
    rw [uniformMeanENN_indicator]
    simp [s, survival, uniformProb]
  have hennmean : poissonGraphMeanENN t (fun G : MGraph V =>
      if Colorable q G then (1 : ℝ≥0∞) else 0) =
      ∑' k, ENNReal.ofReal (w k) * ENNReal.ofReal (s k) := by
    simp only [poissonGraphMeanENN, poissonMixtureENN]
    congr 1
    funext k
    rw [hmeanENN]
  calc
    poissonGraphMeanENN t (fun G : MGraph V =>
        if Colorable q G then (1 : ℝ≥0∞) else 0) =
        ∑' k, ENNReal.ofReal (w k) * ENNReal.ofReal (s k) := hennmean
    _ = ∑' k, ENNReal.ofReal (w k * s k) := by
      congr 1
      funext k
      rw [ENNReal.ofReal_mul (hw k)]
    _ = ENNReal.ofReal (∑' k, w k * s k) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hw k) (hs0 k)) hterms).symm
    _ = ENNReal.ofReal (poissonGraphMean t
        (fun G : MGraph V => indicator (Colorable q G))) := by rw [hrmean]

-- The direct dependencies are kept explicit because this leaf uses their
-- Poisson-series, survival, and measurability conclusions.
theorem S3_54Statement_of_deps
    (h24 : S3_24Statement.{u}) (h31 : S3_31Statement)
    (h39 : S3_39Statement.{u}) :
    S3_54Statement.{u} := by
  intro V _ q hq hN
  let N : ℝ := Fintype.card V
  let C : ℝ := (q : ℝ) ^ Fintype.card V
  let s₀ : ℝ := 2 * (q : ℝ) * N * Real.log (q : ℝ)
  let a : ℝ := 1 - 1 / (2 * (q : ℝ))
  let r : ℝ := 1 / (2 * (q : ℝ))
  let f : ℝ → ℝ := fun t => poissonGraphMean t
    (fun G : MGraph V => indicator (Colorable q G))
  let e : MGraph V → ℝ≥0∞ := fun G => if Colorable q G then 1 else 0
  have hNpos : 0 < (Fintype.card V : ℝ) := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqreal : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hs₀pos : 0 < s₀ := by
    dsimp [s₀, N]
    positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hmix (t : ℝ) : f t =
      ∑' k, poissonWeight t k * survival q (0 : MGraph V) k := by
    simp [f, poissonGraphMean, poissonMixture, survival, uniformProb, uniformMean]
  have hRealNonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
    rw [hmix]
    apply tsum_nonneg
    intro k
    exact mul_nonneg ((h31 t ht).1 k) (survival_nonneg_aux q k)
  have hRealENN (t : ℝ) (ht : 0 ≤ t) :
      (poissonGraphMeanENN t e).toReal = f t := by
    have heq := poissonGraphMeanENN_eq_ofReal (V := V) q h31 t ht
    simpa [e, f, ENNReal.toReal_ofReal (hRealNonneg t ht)] using
      congrArg ENNReal.toReal heq
  have hpoint : ∀ t : ℝ, 0 ≤ t → f t ≤ min 1 (C * Real.exp (-t / (2 * (q : ℝ)))) := by
    intro t ht
    let w : ℕ → ℝ := fun k => poissonWeight t k
    let s : ℕ → ℝ := fun k => survival q (0 : MGraph V) k
    have hw (k : ℕ) : 0 ≤ w k := (h31 t ht).1 k
    have hs0 (k : ℕ) : 0 ≤ s k := survival_nonneg_aux q k
    have hsone (k : ℕ) : s k ≤ 1 := by
      have h := (h24 V q hq (by omega) (0 : MGraph V) k).2.1 (by omega)
      exact le_trans h (min_le_left _ _)
    have hweights : Summable w := by simpa [w] using (h31 t ht).2.1
    have hterms : Summable (fun k => w k * s k) := by
      apply Summable.of_nonneg_of_le (f := w) (g := fun k => w k * s k)
      · intro k
        exact mul_nonneg (hw k) (hs0 k)
      · intro k
        calc
          w k * s k ≤ w k * 1 := mul_le_mul_of_nonneg_left (hsone k) (hw k)
          _ = w k := by ring
      · exact hweights
    have hmix' : f t = ∑' k, w k * s k := by
      simpa [w, s] using hmix t
    have hsum : (∑' k, w k * s k) ≤ 1 := by
      calc
        (∑' k, w k * s k) ≤ ∑' k, w k :=
          hterms.tsum_le_tsum (fun k => by
            calc
              w k * s k ≤ w k * 1 := mul_le_mul_of_nonneg_left (hsone k) (hw k)
              _ = w k := by ring) hweights
        _ = 1 := (h31 t ht).2.2.1
    have hsharp (k : ℕ) : s k ≤ C * a ^ k := by
      have h := (h24 V q hq (by omega) (0 : MGraph V) k).2.2 (by omega)
      simpa [s, C, a] using h
    have ha : 0 ≤ a := by
      dsimp [a]
      have hden : 1 ≤ 2 * (q : ℝ) := by nlinarith [hqreal]
      have hfrac : 1 / (2 * (q : ℝ)) ≤ 1 :=
        (div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ))).2 (by simpa using hden)
      linarith
    have hpgf := (h31 t ht).2.2.2.1 a ha
    have hpgfSum : Summable (fun k => w k * a ^ k) := by simpa [w] using hpgf.1
    have hexpBound : (∑' k, w k * s k) ≤ C * Real.exp (-t / (2 * (q : ℝ))) := by
      calc
        (∑' k, w k * s k) ≤ ∑' k, C * (w k * a ^ k) :=
          hterms.tsum_le_tsum (fun k => by
            calc
              w k * s k ≤ w k * (C * a ^ k) := mul_le_mul_of_nonneg_left (hsharp k) (hw k)
              _ = C * (w k * a ^ k) := by ring) (hpgfSum.mul_left C)
        _ = C * (∑' k, w k * a ^ k) := hpgfSum.tsum_mul_left C
        _ = C * Real.exp (-t / (2 * (q : ℝ))) := by
          rw [hpgf.2]
          congr 1
          have hexp : t * (a - 1) = -t / (2 * (q : ℝ)) := by dsimp [a]; ring
          rw [hexp]
    have hf1 : f t ≤ 1 := by rw [hmix']; exact hsum
    have hf2 : f t ≤ C * Real.exp (-t / (2 * (q : ℝ))) := by rw [hmix']; exact hexpBound
    exact le_min hf1 hf2
  have hfirst : ∀ t : ℝ, 0 ≤ t → f t ≤ min 1 (C * Real.exp (-t / (2 * (q : ℝ)))) := hpoint
  have hmeasENN : Measurable (fun t : ℝ => poissonGraphMeanENN t e) :=
    (h39 V (by omega) e).1
  let g : ℝ → ℝ := fun t => (poissonGraphMeanENN t e).toReal
  have hmeas : Measurable g := hmeasENN.ennreal_toReal
  have hbase : IntegrableOn (fun t : ℝ => C * Real.exp (-r * t)) (Set.Ioi s₀) := by
    have hExp : IntegrableOn (fun t : ℝ => Real.exp ((-r) * t)) (Set.Ioi s₀) :=
      integrableOn_exp_mul_Ioi (by linarith) s₀
    rw [IntegrableOn]
    simpa [smul_eq_mul] using hExp.integrable.const_mul C
  have hbound (t : ℝ) (ht : t ∈ Set.Ioi s₀) : f t ≤ C * Real.exp (-r * t) := by
    have ht0 : 0 ≤ t := le_trans (le_of_lt hs₀pos) (le_of_lt ht)
    calc
      f t ≤ min 1 (C * Real.exp (-t / (2 * (q : ℝ)))) := hfirst t ht0
      _ ≤ C * Real.exp (-t / (2 * (q : ℝ))) := min_le_right _ _
      _ = C * Real.exp (-r * t) := by congr 2 <;> dsimp [r] <;> ring
  have hdom : ∀ᵐ t ∂(volume.restrict (Set.Ioi s₀)), ‖g t‖ ≤ C * Real.exp (-r * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_trans (le_of_lt hs₀pos) (le_of_lt ht)
    calc
      ‖g t‖ = g t := by rw [Real.norm_eq_abs, abs_of_nonneg (ENNReal.toReal_nonneg)]
      _ = f t := hRealENN t ht0
      _ ≤ C * Real.exp (-r * t) := hbound t ht
  have hgInt : Integrable g (volume.restrict (Set.Ioi s₀)) :=
    hbase.integrable.mono' hmeas.aestronglyMeasurable hdom
  have hgIntOn : IntegrableOn g (Set.Ioi s₀) := by
    simpa [IntegrableOn] using hgInt
  have hIntf : IntegrableOn f (Set.Ioi s₀) := by
    apply hgIntOn.congr_fun
    · intro t ht
      exact hRealENN t (le_trans (le_of_lt hs₀pos) (le_of_lt ht))
    · exact measurableSet_Ioi
  have hIntegralLe : (∫ t in Set.Ioi s₀, f t) ≤
      ∫ t in Set.Ioi s₀, C * Real.exp (-r * t) := by
    apply integral_mono_ae hIntf.integrable hbase.integrable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbound t ht
  have hpow : Real.exp (N * Real.log (q : ℝ)) = C := by
    dsimp [C, N]
    rw [← Real.log_pow (q : ℝ) (Fintype.card V)]
    exact Real.exp_log (pow_pos hqpos _)
  have harg : -r * s₀ = -(N * Real.log (q : ℝ)) := by
    dsimp [r, s₀, N]
    field_simp
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hIntegralBase : (∫ t in Set.Ioi s₀, C * Real.exp (-r * t)) = 2 * (q : ℝ) := by
    rw [integral_const_mul]
    rw [integral_exp_mul_Ioi (by linarith) s₀]
    rw [harg, Real.exp_neg, hpow]
    dsimp [r]
    field_simp [hCpos.ne']
  refine ⟨?_,hIntf,?_⟩
  · intro t ht
    simpa [f, C] using hfirst t ht
  · change (∫ t in Set.Ioi s₀, f t) ≤ 2 * (q : ℝ)
    exact le_trans hIntegralLe (le_of_eq hIntegralBase)

end ThLean.W.S377

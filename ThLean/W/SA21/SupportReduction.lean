import ThLean.BP.SA.Interpolation
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA21
open ThresholdFoundations

private theorem tsum_fin_pi_prod (n : ℕ) (f : Fin n → ℕ → ℝ)
    (hs : ∀ i, Summable (fun k => |f i k|)) :
    Summable (fun z : Fin n → ℕ => ∏ i, |f i (z i)|) ∧
    (∑' z : Fin n → ℕ, ∏ i, |f i (z i)|) = ∏ i, ∑' k, |f i k| ∧
    (∑' z : Fin n → ℕ, ∏ i, f i (z i)) = ∏ i, ∑' k, f i k := by
  induction n with
  | zero =>
      constructor
      · exact Summable.of_finite
      constructor
      · simp
      · simp
  | succ n ih =>
      let e₁ : (Fin (n + 1) → ℕ) ≃ (Option (Fin n) → ℕ) :=
        Equiv.piCongrLeft (fun _ => ℕ) (finSuccEquiv n)
      let e₂ : (Option (Fin n) → ℕ) ≃ ℕ × (Fin n → ℕ) :=
        Equiv.piOptionEquivProd (β := fun _ => ℕ)
      let e : (Fin (n + 1) → ℕ) ≃ ℕ × (Fin n → ℕ) := e₁.trans e₂
      let g : ℕ × (Fin n → ℕ) → ℝ := fun p =>
        f 0 p.1 * ∏ i, f i.succ (p.2 i)
      let ga : ℕ × (Fin n → ℕ) → ℝ := fun p =>
        |f 0 p.1| * ∏ i, |f i.succ (p.2 i)|
      have hrest := ih (fun i k => f i.succ k) (fun i => hs i.succ)
      let C : ℝ := ∏ i : Fin n, ∑' k, |f i.succ k|
      have hfiberEq : (fun k : ℕ => ∑' y : Fin n → ℕ,
          |f 0 k| * ∏ i, |f i.succ (y i)|) = fun k => |f 0 k| * C := by
        funext k
        rw [tsum_mul_left]
        simpa [C] using congrArg (fun x : ℝ => |f 0 k| * x) hrest.2.1
      have hfiber : ∀ k : ℕ, Summable (fun y : Fin n → ℕ => |f 0 k| * ∏ i, |f i.succ (y i)|) := by
        intro k
        exact (hrest.1.mul_left |f 0 k|)
      have houter : Summable (fun k : ℕ => ∑' y : Fin n → ℕ, |f 0 k| * ∏ i, |f i.succ (y i)|) := by
        rw [hfiberEq]
        exact (hs 0).mul_right C
      have hga : Summable ga := by
        apply (summable_prod_of_nonneg (fun p => mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _))).2
        exact ⟨hfiber, houter⟩
      have hg : Summable g := by
        apply Summable.of_norm
        simpa [g, ga, Real.norm_eq_abs, abs_mul, Finset.abs_prod] using hga
      have hgaComp : (fun z : Fin (n + 1) → ℕ => ∏ i, |f i (z i)|) = ga ∘ e := by
        funext z
        rw [Fin.prod_univ_succ]
        simp [ga, e, e₁, e₂, Equiv.piCongrLeft, Equiv.piOptionEquivProd,
          finSuccEquiv]
      have habs : Summable (fun z : Fin (n + 1) → ℕ => ∏ i, |f i (z i)|) := by
        rw [hgaComp]
        exact (e.summable_iff).mpr hga
      have hcomp : (fun z : Fin (n + 1) → ℕ => ∏ i, f i (z i)) = g ∘ e := by
        funext z
        rw [Fin.prod_univ_succ]
        simp [g, e, e₁, e₂, Equiv.piCongrLeft, Equiv.piOptionEquivProd,
          finSuccEquiv]
      have hsigned : Summable (fun z : Fin (n + 1) → ℕ => ∏ i, f i (z i)) := by
        apply Summable.of_norm
        simpa [Real.norm_eq_abs, Finset.abs_prod] using habs
      have hsignedPair : Summable g := hg
      constructor
      · exact habs
      constructor
      · calc
          (∑' z : Fin (n + 1) → ℕ, ∏ i, |f i (z i)|)
              = ∑' p : ℕ × (Fin n → ℕ), ga p := by
                  rw [hgaComp]
                  exact e.tsum_eq ga
          _ = ∑' k : ℕ, ∑' y : Fin n → ℕ, |f 0 k| * ∏ i, |f i.succ (y i)| :=
                hga.tsum_prod
          _ = (∑' k : ℕ, |f 0 k|) * C := by
                rw [tsum_congr (fun k => congrFun hfiberEq k), tsum_mul_right]
          _ = ∏ i : Fin (n + 1), ∑' k, |f i k| := by
                simp [C, Fin.prod_univ_succ]
      · calc
          (∑' z : Fin (n + 1) → ℕ, ∏ i, f i (z i))
              = ∑' p : ℕ × (Fin n → ℕ), g p := by
                  rw [hcomp]
                  exact e.tsum_eq g
          _ = ∑' k : ℕ, ∑' y : Fin n → ℕ, f 0 k * ∏ i, f i.succ (y i) :=
                hsignedPair.tsum_prod
          _ = (∑' k : ℕ, f 0 k) * (∏ i : Fin n, ∑' k, f i.succ k) := by
                let C' : ℝ := ∏ i : Fin n, ∑' k, f i.succ k
                have hfiberEqSigned : (fun k : ℕ => ∑' y : Fin n → ℕ,
                    f 0 k * ∏ i, f i.succ (y i)) = fun k => f 0 k * C' := by
                  funext k
                  rw [tsum_mul_left]
                  simpa [C'] using congrArg (fun x : ℝ => f 0 k * x) hrest.2.2
                rw [tsum_congr (fun k => congrFun hfiberEqSigned k), tsum_mul_right]
          _ = ∏ i : Fin (n + 1), ∑' k, f i k := by
                simp [Fin.prod_univ_succ]

private theorem tsum_pi_prod {D : Type} [Fintype D] (f : D → ℕ → ℝ)
    (hs : ∀ d, Summable (fun k => |f d k|)) :
    Summable (fun z : D → ℕ => ∏ d, |f d (z d)|) ∧
    (∑' z : D → ℕ, ∏ d, |f d (z d)|) = ∏ d, ∑' k, |f d k| ∧
    (∑' z : D → ℕ, ∏ d, f d (z d)) = ∏ d, ∑' k, f d k := by
  classical
  let e : D ≃ Fin (Fintype.card D) := Fintype.equivFin D
  let pe : (D → ℕ) ≃ (Fin (Fintype.card D) → ℕ) :=
    Equiv.piCongrLeft (fun _ => ℕ) e
  let f' : Fin (Fintype.card D) → ℕ → ℝ := fun i k => f (e.symm i) k
  have hfin := tsum_fin_pi_prod (Fintype.card D) f' (fun i => hs (e.symm i))
  have habsComp : (fun z : D → ℕ => ∏ d, |f d (z d)|) =
      (fun z : Fin (Fintype.card D) → ℕ => ∏ i, |f' i (z i)|) ∘ pe := by
    funext z
    apply Fintype.prod_equiv e
    intro d
    simp [f', pe, Equiv.piCongrLeft]
  have hcomp : (fun z : D → ℕ => ∏ d, f d (z d)) =
      (fun z : Fin (Fintype.card D) → ℕ => ∏ i, f' i (z i)) ∘ pe := by
    funext z
    apply Fintype.prod_equiv e
    intro d
    simp [f', pe, Equiv.piCongrLeft]
  refine ⟨?_, ?_, ?_⟩
  · rw [habsComp]
    exact (pe.summable_iff).mpr hfin.1
  · calc
      (∑' z : D → ℕ, ∏ d, |f d (z d)|)
          = ∑' z : Fin (Fintype.card D) → ℕ, ∏ i, |f' i (z i)| := by
              rw [habsComp]
              exact pe.tsum_eq (fun z : Fin (Fintype.card D) → ℕ => ∏ i, |f' i (z i)|)
      _ = ∏ i, ∑' k, |f' i k| := hfin.2.1
      _ = ∏ d, ∑' k, |f d k| := by
            symm
            apply Fintype.prod_equiv e
            intro d
            simp [f']
  · calc
      (∑' z : D → ℕ, ∏ d, f d (z d))
          = ∑' z : Fin (Fintype.card D) → ℕ, ∏ i, f' i (z i) := by
              rw [hcomp]
              exact pe.tsum_eq (fun z : Fin (Fintype.card D) → ℕ => ∏ i, f' i (z i))
      _ = ∏ i, ∑' k, f' i k := hfin.2.2
      _ = ∏ d, ∑' k, f d k := by
            symm
            apply Fintype.prod_equiv e
            intro d
            simp [f']

private theorem poissonWeight_abs_summable (r : ℝ) :
    Summable (fun k : ℕ => |poissonWeight r k|) := by
  have h := (Real.summable_pow_div_factorial |r|).mul_left (Real.exp (-r))
  refine h.congr ?_
  intro k
  simp [poissonWeight, abs_div, abs_mul, abs_pow]
  ring

private theorem poissonWeight_tsum (r : ℝ) :
    (∑' k : ℕ, poissonWeight r k) = 1 := by
  calc
    (∑' k : ℕ, poissonWeight r k) = Real.exp (-r) * Real.exp r := by
      simpa [poissonWeight, mul_div_assoc, Real.exp_eq_exp_ℝ] using
        ((NormedSpace.expSeries_div_hasSum_exp r).mul_left (Real.exp (-r))).tsum_eq
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

private theorem poissonWeight_zero_tsum (r : ℝ) :
    (∑' k : ℕ, if k = 0 then poissonWeight r k else 0) = Real.exp (-r) := by
  rw [tsum_ite_eq 0 (fun k : ℕ => poissonWeight r k)]
  simp [poissonWeight]

private theorem poissonWeight_pos_tsum (r : ℝ) :
    (∑' k : ℕ, if 0 < k then poissonWeight r k else 0) = 1 - Real.exp (-r) := by
  have hs : Summable (fun k : ℕ => poissonWeight r k) := by
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using poissonWeight_abs_summable r
  have hsplit := hs.tsum_eq_add_tsum_ite 0
  have hzero : poissonWeight r 0 = Real.exp (-r) := by simp [poissonWeight]
  have htail : (∑' k : ℕ, if k = 0 then 0 else poissonWeight r k) =
      1 - Real.exp (-r) := by
    linarith [hsplit, poissonWeight_tsum r, hzero]
  calc
    (∑' k : ℕ, if 0 < k then poissonWeight r k else 0) =
        ∑' k : ℕ, if k = 0 then 0 else poissonWeight r k := by
      apply tsum_congr
      intro k
      by_cases hk : k = 0 <;> simp [hk]
    _ = 1 - Real.exp (-r) := htail

private theorem poissonSupportFiber_tsum {D : Type} [Fintype D] [DecidableEq D]
    (rate : D → ℝ) (T : Finset D) :
    Summable (fun z : D → ℕ =>
      if Finset.univ.filter (fun e => 0 < z e) = T then
        ∏ e, poissonWeight (rate e) (z e) else 0) ∧
    (∑' z : D → ℕ,
      if Finset.univ.filter (fun e => 0 < z e) = T then
        ∏ e, poissonWeight (rate e) (z e) else 0) =
      ThresholdFoundations.poissonSupportWeight rate T := by
  classical
  let supp : (D → ℕ) → Finset D := fun z => Finset.univ.filter (fun e => 0 < z e)
  let coord : D → ℕ → ℝ := fun e k =>
    if (e ∈ T ↔ 0 < k) then poissonWeight (rate e) k else 0
  have hcoord : ∀ e, Summable (fun k : ℕ => |coord e k|) := by
    intro e
    apply Summable.of_norm_bounded (poissonWeight_abs_summable (rate e))
    intro k
    by_cases h : (e ∈ T ↔ 0 < k) <;> simp [coord, h, Real.norm_eq_abs]
  have hpi := tsum_pi_prod coord hcoord
  have hterm : ∀ z : D → ℕ,
      (if supp z = T then ∏ e, poissonWeight (rate e) (z e) else 0) =
        ∏ e, coord e (z e) := by
    intro z
    rw [Fintype.prod_ite_zero]
    by_cases h : ∀ e, (e ∈ T ↔ 0 < z e)
    · have hs : supp z = T := by
        apply Finset.ext
        intro e
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (h e).symm
      simp [h, hs]
    · have hs : supp z ≠ T := by
        intro hs
        apply h
        intro e
        have he : e ∈ supp z ↔ e ∈ T := by simp [hs]
        have he' : 0 < z e ↔ e ∈ T := by simpa [supp] using he
        exact he'.symm
      simp [h, hs]
  have hcoordSum : ∀ e,
      (∑' k : ℕ, coord e k) =
        if e ∈ T then 1 - Real.exp (-(rate e)) else Real.exp (-(rate e)) := by
    intro e
    by_cases he : e ∈ T
    · simpa [coord, he] using poissonWeight_pos_tsum (rate e)
    · simpa [coord, he] using poissonWeight_zero_tsum (rate e)
  have hsum : (∏ e, ∑' k : ℕ, coord e k) =
      ThresholdFoundations.poissonSupportWeight rate T := by
    calc
      (∏ e, ∑' k : ℕ, coord e k) =
          ∏ e, if e ∈ T then 1 - Real.exp (-(rate e)) else Real.exp (-(rate e)) := by
            apply Fintype.prod_congr
            intro e
            exact hcoordSum e
      _ = ThresholdFoundations.poissonSupportWeight rate T := by
            rw [Finset.prod_ite]
            have hT : Finset.univ.filter (fun e : D => e ∈ T) = T := by
              ext e
              simp
            have hTcompl : Finset.univ.filter (fun e : D => ¬ e ∈ T) =
                Finset.univ \ T := by
              ext e
              simp
            rw [hT, hTcompl]
            unfold ThresholdFoundations.poissonSupportWeight
            apply congrArg (fun x : ℝ =>
              (∏ e ∈ T, (1 - Real.exp (-(rate e)))) * x)
            apply Finset.prod_congr
            · ext e
              simp
            · intro e he
              rfl
  refine ⟨?_, ?_⟩
  · have hsigned : Summable (fun z : D → ℕ => ∏ e, coord e (z e)) := by
      apply Summable.of_norm
      simpa [Real.norm_eq_abs, Finset.abs_prod] using hpi.1
    rw [show (fun z : D → ℕ =>
      if supp z = T then ∏ e, poissonWeight (rate e) (z e) else 0) =
      (fun z : D → ℕ => ∏ e, coord e (z e)) by funext z; exact hterm z]
    exact hsigned
  · calc
      (∑' z : D → ℕ,
        if supp z = T then ∏ e, poissonWeight (rate e) (z e) else 0)
          = ∑' z : D → ℕ, ∏ e, coord e (z e) := by
              apply tsum_congr
              intro z
              exact hterm z
      _ = ∏ e, ∑' k : ℕ, coord e k := hpi.2.2
      _ = ThresholdFoundations.poissonSupportWeight rate T := hsum

theorem SA_I11bStatement_holds : ThLean.BP.SA.SA_I11bStatement := by
  intro D instD instEq rate F
  classical
  let supp : (D → ℕ) → Finset D := fun z => Finset.univ.filter (fun e => 0 < z e)
  let weight : (D → ℕ) → ℝ := fun z => ∏ e, poissonWeight (rate e) (z e)
  let U : Finset (Finset D) := Finset.univ.powerset
  let P := {T : Finset D // T ∈ U}
  let B : ℝ := ∑ T ∈ U, |F T|
  let coeff : Finset D → (D → ℕ) → ℝ := fun T z =>
    if supp z = T then weight z * F T else 0
  have hB : 0 ≤ B := by
    exact Finset.sum_nonneg (fun T hT => abs_nonneg (F T))
  have hFbound : ∀ T, T ∈ U → |F T| ≤ B := by
    intro T hT
    exact Finset.single_le_sum (fun S hS => abs_nonneg (F S)) hT
  have hbase := tsum_pi_prod (fun e k => poissonWeight (rate e) k)
    (fun e => poissonWeight_abs_summable (rate e))
  have hExpand : ∀ z : D → ℕ,
      weight z * F (supp z) = ∑ T ∈ U, coeff T z := by
    intro z
    calc
      weight z * F (supp z) = coeff (supp z) z := by simp [coeff]
      _ = ∑ T ∈ U, coeff T z := by
        symm
        apply Finset.sum_eq_single (supp z)
        · intro T hT hne
          simp [coeff, hne.symm]
        · intro hnot
          exact (hnot (Finset.mem_powerset.mpr (Finset.subset_univ _))).elim
  have hCoeffAbs : ∀ T, T ∈ U → Summable (fun z : D → ℕ => |coeff T z|) := by
    intro T hT
    apply Summable.of_nonneg_of_le (fun z => abs_nonneg (coeff T z)) ?_
      (hbase.1.mul_left B)
    intro z
    by_cases hz : supp z = T
    · simp [coeff, hz, weight, abs_mul, Finset.abs_prod]
      calc
        (∏ e, |poissonWeight (rate e) (z e)|) * |F T|
            ≤ (∏ e, |poissonWeight (rate e) (z e)|) * B := by
                exact mul_le_mul_of_nonneg_left (hFbound T hT)
                  (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        _ = B * ∏ e, |poissonWeight (rate e) (z e)| := by ring
    · simp [coeff, hz]
      exact mul_nonneg hB (Finset.prod_nonneg fun _ _ => abs_nonneg _)
  let pairTerm : P → (D → ℕ) → ℝ := fun T z => coeff T.1 z
  have hpairAbs : Summable (fun p : P × (D → ℕ) => |pairTerm p.1 p.2|) := by
    apply (summable_prod_of_nonneg (fun p => abs_nonneg (pairTerm p.1 p.2))).2
    constructor
    · intro T
      exact hCoeffAbs T.1 T.2
    · exact Summable.of_finite
  have hpair : Summable (Function.uncurry pairTerm) := by
    apply Summable.of_norm
    simpa [Function.uncurry, Real.norm_eq_abs] using hpairAbs
  have hswap : (∑' z : D → ℕ, ∑ T : P, pairTerm T z) =
      ∑ T : P, ∑' z : D → ℕ, pairTerm T z := by
    simpa only [tsum_fintype] using hpair.tsum_comm
  have hCoeffMean : ∀ T : P,
      (∑' z : D → ℕ, pairTerm T z) =
        ThresholdFoundations.poissonSupportWeight rate T.1 * F T.1 := by
    intro T
    have hfiber := poissonSupportFiber_tsum rate T.1
    have hpoint : ∀ z : D → ℕ,
        pairTerm T z =
          (if supp z = T.1 then weight z else 0) * F T.1 := by
      intro z
      by_cases hz : supp z = T.1 <;> simp [pairTerm, coeff, hz]
    calc
      (∑' z : D → ℕ, pairTerm T z)
          = (∑' z : D → ℕ, if supp z = T.1 then weight z else 0) * F T.1 := by
              calc
                (∑' z : D → ℕ, pairTerm T z) =
                    ∑' z : D → ℕ, (if supp z = T.1 then weight z else 0) * F T.1 := by
                      apply tsum_congr
                      exact hpoint
                _ = (∑' z : D → ℕ, if supp z = T.1 then weight z else 0) * F T.1 :=
                      tsum_mul_right
      _ = ThresholdFoundations.poissonSupportWeight rate T.1 * F T.1 := by
            rw [show (fun z : D → ℕ => if supp z = T.1 then weight z else 0) =
              (fun z => if Finset.univ.filter (fun e => 0 < z e) = T.1 then
                ∏ e, poissonWeight (rate e) (z e) else 0) by
                funext z
                simp [supp, weight]]
            exact congrArg (fun x : ℝ => x * F T.1) hfiber.2
  constructor
  · apply Summable.of_norm_bounded (hbase.1.mul_left B)
    intro z
    calc
      ‖weight z * F (supp z)‖ =
          (∏ e, |poissonWeight (rate e) (z e)|) * |F (supp z)| := by
            simp [weight, Real.norm_eq_abs]
      _ ≤ (∏ e, |poissonWeight (rate e) (z e)|) * B := by
            apply mul_le_mul_of_nonneg_left _
              (Finset.prod_nonneg fun _ _ => abs_nonneg _)
            exact hFbound (supp z) (Finset.mem_powerset.mpr (Finset.subset_univ _))
      _ = B * ∏ e, |poissonWeight (rate e) (z e)| := by ring
  · calc
      (∑' z : D → ℕ, weight z * F (supp z))
          = ∑' z : D → ℕ, ∑ T ∈ U, coeff T z := by
              apply tsum_congr
              exact hExpand
      _ = ∑' z : D → ℕ, ∑ T : P, pairTerm T z := by
              apply tsum_congr
              intro z
              rw [Finset.sum_subtype U (fun T => Iff.rfl)]
      _ = ∑ T : P, ∑' z : D → ℕ, pairTerm T z := hswap
      _ = ∑ T ∈ U, ThresholdFoundations.poissonSupportWeight rate T * F T := by
              rw [Finset.sum_subtype U (fun T => Iff.rfl)]
              apply Finset.sum_congr rfl
              intro T hT
              exact hCoeffMean T
      _ = ThresholdFoundations.poissonSupportMean rate F := rfl

end ThLean.W.SA21

import ThLean.BP.S3.Terminal

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S322
open ThresholdFoundations ThLean.BP.S3

private lemma sym2_relabel_left {V : Type*} (π : Equiv.Perm V) (e : Sym2 V) :
    Sym2.map π.symm (Sym2.map π e) = e := by
  calc
    Sym2.map π.symm (Sym2.map π e) = (Sym2.map π.symm ∘ Sym2.map π) e := rfl
    _ = Sym2.map (π.symm ∘ π) e := by rw [← Sym2.map_comp]
    _ = e := by
      rw [show π.symm ∘ π = id by ext v; simp]
      simp

private lemma sym2_relabel_right {V : Type*} (π : Equiv.Perm V) (e : Sym2 V) :
    Sym2.map π (Sym2.map π.symm e) = e := by
  calc
    Sym2.map π (Sym2.map π.symm e) = (Sym2.map π ∘ Sym2.map π.symm) e := rfl
    _ = Sym2.map (π ∘ π.symm) e := by rw [← Sym2.map_comp]
    _ = e := by
      rw [show π ∘ π.symm = id by ext v; simp]
      simp

private lemma relabel_perm_apply {V : Type*} [Fintype V] (π : Equiv.Perm V)
    (G : MGraph V) (e : Sym2 V) :
    relabel π G e = G (Sym2.map π.symm e) := by
  classical
  unfold relabel mapGraph
  have hleft := sym2_relabel_left π
  have hmap := sym2_relabel_right π e
  have hiff (x : Sym2 V) : Sym2.map π x = e ↔ x = Sym2.map π.symm e := by
    constructor
    · intro hx
      calc
        x = Sym2.map π.symm (Sym2.map π x) := (hleft x).symm
        _ = Sym2.map π.symm e := by rw [hx]
    · intro hx
      rw [hx]
      exact hmap
  calc
    (∑ x, if Sym2.map π x = e then G x else 0) =
        ∑ x, if x = Sym2.map π.symm e then G x else 0 := by
          simp_rw [hiff]
    _ = G (Sym2.map π.symm e) := by simp

private def relabelGraphEquiv {V : Type*} [Fintype V] (π : Equiv.Perm V) :
    MGraph V ≃ MGraph V where
  toFun := relabel π
  invFun := relabel π.symm
  left_inv := by
    intro G
    ext e
    rw [relabel_perm_apply]
    simp only [Equiv.symm_symm]
    rw [relabel_perm_apply, sym2_relabel_left]
  right_inv := by
    intro G
    ext e
    rw [relabel_perm_apply, relabel_perm_apply]
    rw [show (π.symm).symm = π from Equiv.symm_symm π]
    exact congrArg G (sym2_relabel_right π e)

theorem S3_19bStatement_of_deps (h03 : S3_03aStatement.{u})
    (h19a : S3_19aStatement.{u}) :
    S3_19bStatement.{u} := by
  intro V _ q hq hV A h ν hAdm hA hInv hν e
  let N : ℝ≥0∞ := Fintype.card (Pair V)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (h03 V hV).2.1
  have hNreal : (0 : ℝ) < Fintype.card (Pair V) :=
    Nat.cast_pos.mpr (h03 V hV).2.1
  have hK (G : MGraph V) :
      ENNReal.ofReal (kappaKind q A G) =
        (∑ f : Pair V, if A G f then (1 : ℝ≥0∞) else 0) / N := by
    have hKr : kappaKind q A G =
        (∑ f : Pair V, if A G f then (1 : ℝ) else 0) /
          (Fintype.card (Pair V) : ℝ) := by
      unfold kappaKind uniformProb uniformMean
      congr 1
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hAf : A G f
      · simp [indicator, hAf, hAdm G f hAf]
      · simp [indicator, hAf]
    rw [hKr, ENNReal.ofReal_div_of_pos hNreal]
    rw [ENNReal.ofReal_sum_of_nonneg (by
      intro f hf
      split <;> positivity)]
    have hsum :
        (∑ f : Pair V, ENNReal.ofReal (if A G f then (1 : ℝ) else 0)) =
          ∑ f : Pair V, if A G f then (1 : ℝ≥0∞) else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hAf : A G f <;> simp [hAf]
    rw [hsum]
    simp [N]
  have hfixed (f : Pair V) :
      (∑' G : MGraph V, ν G * (if A G f then h G else 0)) =
      (∑' G : MGraph V, ν G * (if A G e then h G else 0)) := by
    obtain ⟨π, hπ⟩ := h19a V f e
    have hterm (G : MGraph V) :
        ν G * (if A G f then h G else 0) =
          ν (relabel π G) * (if A (relabel π G) e then h (relabel π G) else 0) := by
      have hAi : A (relabel π G) e ↔ A G f := hA π G f e hπ
      rw [← hν π G]
      have hh : h (relabel π G) = h G := hInv π G
      rw [← hh]
      simp [hAi]
    calc
      (∑' G : MGraph V, ν G * (if A G f then h G else 0)) =
          ∑' G : MGraph V,
            ν (relabel π G) * (if A (relabel π G) e then h (relabel π G) else 0) := by
              apply tsum_congr
              intro G
              exact hterm G
      _ = ∑' G : MGraph V, ν G * (if A G e then h G else 0) := by
        exact (relabelGraphEquiv π).tsum_eq
          (fun G : MGraph V => ν G * (if A G e then h G else 0))
  have hpoint (G : MGraph V) :
      ν G * ((∑ f : Pair V, if A G f then (1 : ℝ≥0∞) else 0) / N * h G) =
        (∑ f : Pair V, ν G * (if A G f then h G else 0)) / N := by
    simp only [div_eq_mul_inv]
    calc
      ν G * ((∑ f : Pair V, if A G f then (1 : ℝ≥0∞) else 0) * N⁻¹ * h G) =
          (ν G * (∑ f : Pair V, if A G f then (1 : ℝ≥0∞) else 0) * h G) * N⁻¹ := by
            ac_rfl
      _ = (∑ f : Pair V,
          (ν G * (if A G f then (1 : ℝ≥0∞) else 0)) * h G) * N⁻¹ := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = (∑ f : Pair V, ν G * (if A G f then h G else 0)) * N⁻¹ := by
            congr 1
            apply Finset.sum_congr rfl
            intro f hf
            by_cases hAf : A G f <;> simp [hAf, mul_assoc]
  have hswap (F : MGraph V → Pair V → ℝ≥0∞) :
      (∑' G : MGraph V, ∑ f : Pair V, F G f) =
        ∑ f : Pair V, ∑' G : MGraph V, F G f := by
    calc
      (∑' G : MGraph V, ∑ f : Pair V, F G f) =
          ∑' G : MGraph V, ∑' f : Pair V, F G f := by
            congr 1
            funext G
            exact (tsum_fintype (fun f : Pair V => F G f)).symm
      _ = ∑' f : Pair V, ∑' G : MGraph V, F G f := ENNReal.tsum_comm
      _ = ∑ f : Pair V, ∑' G : MGraph V, F G f := by
            exact tsum_fintype _
  have hdiv (F : MGraph V → ℝ≥0∞) :
      (∑' G : MGraph V, F G / N) = (∑' G : MGraph V, F G) / N := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right]
  calc
    (∑' G : MGraph V, ν G * (ENNReal.ofReal (kappaKind q A G) * h G)) =
        ∑' G : MGraph V,
          (∑ f : Pair V, ν G * (if A G f then h G else 0)) / N := by
            apply tsum_congr
            intro G
            rw [hK G]
            exact hpoint G
    _ = (∑ f : Pair V,
          ∑' G : MGraph V, ν G * (if A G f then h G else 0)) / N := by
            rw [hdiv]
            exact congrArg (fun x : ℝ≥0∞ => x / N)
              (hswap (fun G f => ν G * (if A G f then h G else 0)))
    _ = ∑' G : MGraph V, ν G * (if A G e then h G else 0) := by
            have hsum :
                (∑ f : Pair V, ∑' G : MGraph V,
                    ν G * (if A G f then h G else 0)) =
                  (Fintype.card (Pair V) : ℝ≥0∞) *
                    (∑' G : MGraph V, ν G * (if A G e then h G else 0)) := by
              calc
                _ = ∑ f : Pair V,
                    (∑' G : MGraph V, ν G * (if A G e then h G else 0)) := by
                      apply Finset.sum_congr rfl
                      intro f hf
                      exact hfixed f
                _ = _ := by simp [Finset.sum_const]
            rw [hsum]
            change (N * (∑' G : MGraph V, ν G * (if A G e then h G else 0))) / N = _
            rw [mul_div_assoc]
            exact ENNReal.mul_div_cancel hN.ne' (by
              simpa [N] using ENNReal.natCast_ne_top (Fintype.card (Pair V)))

end ThLean.W.S322

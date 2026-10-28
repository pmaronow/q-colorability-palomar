import ThLean.W.S523S.Kernels
import ThLean.W.S523S.GraphSplit

noncomputable section
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S523S
open ThresholdFoundations ThLean.BP.S5

theorem uniformMean_abs_bound {A : Type} [Fintype A] [Nonempty A]
    {C : ℝ} {f : A → ℝ} (hf : ∀ a, |f a| ≤ C) : |uniformMean f| ≤ C := by
  have hc : 0 < (Fintype.card A : ℝ) := by positivity
  unfold uniformMean
  rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
  calc
    |∑ a, f a| ≤ ∑ a, |f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : A, C := Finset.sum_le_sum (fun a _ => hf a)
    _ = C * (Fintype.card A : ℝ) := by simp [mul_comm]

theorem blocking_abs_bound {V : Type} [Fintype V] [Nonempty V]
    (q : ℕ) (B : MGraph V) (j : ℕ) : |blocking q B j| ≤ 1 := by
  classical
  exact uniformMean_abs_bound (fun _ => (indicator_bounds _).2)

theorem mixture_abs_bound {z C : ℝ} (hz : 0 ≤ z) {f : ℕ → ℝ}
    (hf : ∀ j, |f j| ≤ C) : |poissonMixture z f| ≤ C := by
  have hd (j : ℕ) : ‖poissonWeight z j * f j‖ ≤ C * poissonWeight z j := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg hz j)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hf j) (weight_nonneg hz j)
  simpa [poissonMixture, Real.norm_eq_abs] using
    tsum_of_norm_bounded ((weight_hasSum z).mul_left C) hd

theorem mean_reindex {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (r : J → ℝ) (f : (J → ℕ) → ℝ) :
    mean r f = mean (r ∘ e) (fun x => f (fun j => x (e.symm j))) := by
  classical
  let E : (I → ℕ) ≃ (J → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
  unfold mean
  rw [← E.tsum_eq (fun x => mass r x * f x)]
  apply tsum_congr
  intro x
  have hm : mass r (E x) = mass (r ∘ e) x := by
    simpa [mass, E, Equiv.arrowCongr, Function.comp_def] using
      (e.prod_comp (fun j => poissonWeight (r j) (x (e.symm j)))).symm
  rw [hm]
  rfl

theorem crossing_aggregation (h09c : S5_09CStatement)
    (A V : Type) [Fintype A] [Fintype V] [Nonempty V]
    (r : ℝ) (hr : 0 ≤ r) (f : (V → ℕ) → ℝ) (hf : ∃ C, ∀ x, |f x| ≤ C) :
    mean (fun _ : A × V => r) (fun c => f (fun v => ∑ a, c (a, v))) =
      poissonMixture (Fintype.card A * Fintype.card V * r) (fun j =>
        uniformMean (fun x : Fin j → V =>
          f (fun v => (Finset.univ.filter (fun i => x i = v)).card))) := by
  classical
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  rw [mean_reindex (e.prodCongr (Equiv.refl V))]
  have ha (c : Fin (Fintype.card A) × V → ℕ) :
      (fun v => ∑ a : A, c (e.symm a, v)) = (fun v => ∑ i, c (i, v)) := by
    funext v
    exact e.symm.sum_comp (fun i => c (i, v))
  change mean (fun _ : Fin (Fintype.card A) × V => r)
    (fun c => f (fun v => ∑ a : A, c (e.symm a, v))) = _
  simp_rw [ha]
  exact h09c V (Fintype.card A) r hr f hf

theorem addRoot_countsList_ofFn {V : Type} [Fintype V] (B : MGraph V)
    {j : ℕ} (x : Fin j → V) :
    addRoot B (countsList (fun v => (Finset.univ.filter (fun i => x i = v)).card)) =
      addRoot B (List.ofFn x) := by
  classical
  have hp : (countsList (fun v => (Finset.univ.filter (fun i => x i = v)).card)).Perm
      (List.ofFn x) := by
    apply List.perm_iff_count.mpr
    intro v
    rw [countsList_count, countsList_ofFn]
  ext e
  dsimp only [addRoot, ThresholdFoundations.star, Pi.add_apply]
  rw [(hp.map (fun v => s(none, some v))).count_eq e]

theorem crossing_blocking (h09c : S5_09CStatement)
    (A V : Type) [Fintype A] [Fintype V] [Nonempty V]
    (q : ℕ) (B : MGraph V) (r : ℝ) (hr : 0 ≤ r) :
    mean (fun _ : A × V => r) (fun c => indicator (Colorable q B ∧
      ¬ Colorable q (addRoot B (countsList (fun v => ∑ a, c (a, v)))))) =
      poissonMixture (Fintype.card A * Fintype.card V * r) (blocking q B) := by
  classical
  have h := crossing_aggregation h09c A V r hr
    (fun d => indicator (Colorable q B ∧ ¬Colorable q (addRoot B (countsList d))))
    ⟨1, fun _ => (indicator_bounds _).2⟩
  change mean _ _ = poissonMixture _ (fun j => uniformMean (fun x : Fin j → V =>
    indicator (Colorable q B ∧ ¬Colorable q (addRoot B (List.ofFn x)))))
  simpa only [addRoot_countsList_ofFn] using h

theorem addedFailure_comm {V : Type} [Fintype V] [Nonempty V]
    (q : ℕ) {r z : ℝ} (hr : 0 ≤ r) (hz : 0 ≤ z) :
    countMean r (fun B : MGraph V => poissonMixture z (blocking q B)) =
      addedFailure (V := V) q r z := by
  change (∑' B, mass (perPairRate r) B * ∑' j, poissonWeight z j * blocking q B j) =
    ∑' j, poissonWeight z j * ∑' B, mass (perPairRate r) B * blocking q B j
  exact weighted_comm _ _ (mass_hasSum _ _ (perPairRate_nonneg hr)).summable
    (weight_hasSum z).summable (mass_nonneg (perPairRate_nonneg hr))
    (weight_nonneg hz) _ ⟨1, fun B j => blocking_abs_bound q B j⟩

end ThLean.W.S523S

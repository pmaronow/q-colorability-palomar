module

public import ThLean.BP.S5.Poisson

@[expose] public section

noncomputable section
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S551S

open ThresholdFoundations

/-- Push a finite uniform mean through any map into a possibly infinite set. -/
lemma uniform_pushforward_hasSum {A B : Type*} [Fintype A]
    (g : A → B) (f : B → ℝ) :
    HasSum (fun b => uniformProb (fun a => g a = b) * f b)
      (uniformMean (fun a => f (g a))) := by
  classical
  have h (a : A) : HasSum (fun b => indicator (g a = b) * f b) (f (g a)) := by
    have he : (fun b => indicator (g a = b) * f b) =
        (fun b => if b = g a then f (g a) else 0) := by
      funext b
      by_cases hb : b = g a <;> simp [indicator, hb, eq_comm]
    rw [he]
    exact hasSum_ite_eq (g a) (f (g a))
  have hs := (hasSum_sum (s := Finset.univ) (fun a _ => h a)).div_const
    (Fintype.card A : ℝ)
  unfold uniformProb uniformMean
  convert hs using 1
  funext b
  rw [div_mul_eq_mul_div, Finset.sum_mul]

lemma poisson_summable (t : ℝ) : Summable (poissonWeight t) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (t : ℝ)).mul_left (Real.exp (-t))
  convert h.summable using 1
  funext j
  exact mul_div_assoc _ _ _

def histogram {E : Type*} [Fintype E] {m : ℕ} (x : Fin m → E) : E → ℕ :=
  fun e => (Finset.univ.filter (fun i => x i = e)).card

/-- Point probabilities for a Poisson histogram determine every bounded real mean.
The double series is absolutely summable before its order is exchanged. -/
lemma poisson_histogram_mean
    (h08A : ThLean.BP.S5.S5_08AStatement)
    (E : Type) [Fintype E] [Nonempty E] (t : ℝ) (ht : 0 ≤ t)
    (f : (E → ℕ) → ℝ) (hf : ∃ C : ℝ, ∀ c, |f c| ≤ C) :
    (∑' c : E → ℕ, (∏ e, poissonWeight (t / Fintype.card E) (c e)) * f c) =
      poissonMixture t (fun m => uniformMean (fun x : Fin m → E => f (histogram x))) := by
  classical
  let P (m : ℕ) (c : E → ℕ) : ℝ :=
    poissonWeight t m * uniformProb (fun x : Fin m → E => histogram x = c)
  have hpos (m : ℕ) (c : E → ℕ) : 0 ≤ P m c := by
    dsimp [P]
    unfold poissonWeight uniformProb uniformMean indicator
    positivity
  have hpoint (c : E → ℕ) : HasSum (fun m => P m c)
      (∏ e, poissonWeight (t / Fintype.card E) (c e)) := by
    simpa only [P, histogram, funext_iff] using h08A E t ht c
  have hrow (m : ℕ) : HasSum (P m) (poissonWeight t m) := by
    have h := (uniform_pushforward_hasSum
      (fun x : Fin m → E => histogram x) (fun _ => (1 : ℝ))).mul_left
        (poissonWeight t m)
    have hc : (Fintype.card (Fin m → E) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simpa [P, uniformMean, hc] using h
  have hmatrix : Summable (Function.uncurry P) := by
    apply (summable_prod_of_nonneg (fun p => hpos p.1 p.2)).2
    refine ⟨fun m => (hrow m).summable, ?_⟩
    exact (poisson_summable t).congr (fun m => (hrow m).tsum_eq.symm)
  obtain ⟨C, hC⟩ := hf
  have hweighted : Summable
      (fun p : ℕ × (E → ℕ) => P p.1 p.2 * f p.2) := by
    apply (hmatrix.mul_right C).of_norm_bounded
    intro p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos p.1 p.2)]
    exact mul_le_mul_of_nonneg_left (hC p.2) (hpos p.1 p.2)
  calc
    (∑' c : E → ℕ, (∏ e, poissonWeight (t / Fintype.card E) (c e)) * f c) =
        ∑' c, ∑' m, P m c * f c := by
      apply tsum_congr
      intro c
      rw [tsum_mul_right, (hpoint c).tsum_eq]
    _ = ∑' m, ∑' c, P m c * f c := hweighted.tsum_comm
    _ = poissonMixture t (fun m =>
        uniformMean (fun x : Fin m → E => f (histogram x))) := by
      apply tsum_congr
      intro m
      simp only [P, mul_assoc, tsum_mul_left]
      rw [(uniform_pushforward_hasSum (fun x : Fin m → E => histogram x) f).tsum_eq]

end ThLean.W.S551S

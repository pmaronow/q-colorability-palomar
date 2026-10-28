import ThLean.BP.SA.Analytic
import Mathlib.Topology.EMetricSpace.Basic

noncomputable section
open Filter
open scoped BigOperators Topology

namespace ThLean.W.SA32

open ThLean.BP.SA
open ThresholdFoundations

private def derivativeBox (N : ℕ) : Finset (Fin 3 → ℕ) :=
  Finset.univ.image (fun x : Fin 3 → Fin N => fun i => (x i).val)

private theorem derivativeBox_mono : Monotone derivativeBox := by
  intro N M hNM k hk
  rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨fun i => Fin.castLE hNM (x i), Finset.mem_univ _, ?_⟩
  funext i
  simp

private theorem derivativeBox_covers (k : Fin 3 → ℕ) :
    ∃ N, k ∈ derivativeBox N := by
  let N := max (k 0) (max (k 1) (k 2)) + 1
  let x : Fin 3 → Fin N := fun i =>
    ⟨k i, by fin_cases i <;> simp [N]⟩
  refine ⟨N, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, ?_⟩⟩
  funext i
  simp [x]

private theorem tendsto_derivativeBox : Tendsto derivativeBox atTop atTop :=
  Filter.tendsto_atTop_finset_of_monotone derivativeBox_mono derivativeBox_covers

private def derivativeNormTerm (q n₁ n₂ r : ℕ) (k : Fin 3 → ℕ)
    (μ : Fin 3 → ℝ) : ℝ :=
  ‖iteratedFDeriv ℝ r (interpolationTerm q n₁ n₂ k) μ‖

private theorem derivativePartial_eq_box (q n₁ n₂ r N : ℕ) (μ : Fin 3 → ℝ) :
    interpolationDerivativeNormPartial q n₁ n₂ r N μ =
      ∑ k ∈ derivativeBox N, derivativeNormTerm q n₁ n₂ r k μ := by
  classical
  unfold interpolationDerivativeNormPartial derivativeBox derivativeNormTerm
  exact (Finset.sum_image
    (s := Finset.univ)
    (g := fun x : Fin 3 → Fin N => fun i => (x i).val)
    (f := fun k : Fin 3 → ℕ =>
      ‖iteratedFDeriv ℝ r (interpolationTerm q n₁ n₂ k) μ‖)
    (by
      intro x hx y hy hxy
      funext i
      exact Fin.ext (congrFun hxy i))).symm

private theorem derivativeNormSeries_uniformOn
    (he : SA_I13eStatement) (hf : SA_I13fStatement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (r : ℕ) (μ₀ : Fin 3 → ℝ) :
    TendstoUniformlyOn
      (interpolationDerivativeNormPartial q n₁ n₂ r)
      (fun μ => ∑' k : Fin 3 → ℕ, derivativeNormTerm q n₁ n₂ r k μ)
      atTop (Metric.ball μ₀ 1) := by
  classical
  let R : ℝ := ‖μ₀‖ + 1
  have hR : 0 ≤ R := by positivity
  obtain ⟨C, hC, hbound⟩ := he q n₁ n₂ hq hn₁ hn₂ R hR r
  have hmajorant : Summable (fun k : Fin 3 → ℕ => C * poissonMajorant R r k) :=
    (hf R hR r).mul_left C
  have hboxBound : ∀ μ ∈ Metric.ball μ₀ 1, ∀ i : Fin 3, |μ i| ≤ R := by
    intro μ hμ i
    have hdist : ‖μ - μ₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hμ
    have hi : ‖(μ - μ₀) i‖ ≤ ‖μ - μ₀‖ := norm_le_pi_norm (μ - μ₀) i
    have hcoord : ‖μ i‖ ≤ ‖μ₀‖ + 1 := by
      calc
        ‖μ i‖ = ‖μ₀ i + (μ - μ₀) i‖ := by congr 1; simp
        _ ≤ ‖μ₀ i‖ + ‖(μ - μ₀) i‖ := norm_add_le _ _
        _ ≤ ‖μ₀‖ + 1 := add_le_add (norm_le_pi_norm μ₀ i) (le_of_lt (hi.trans_lt hdist))
    simpa [R, Real.norm_eq_abs] using hcoord
  have huniform : TendstoUniformlyOn
      (fun t : Finset (Fin 3 → ℕ) => fun μ =>
        ∑ k ∈ t, derivativeNormTerm q n₁ n₂ r k μ)
      (fun μ => ∑' k : Fin 3 → ℕ, derivativeNormTerm q n₁ n₂ r k μ)
      atTop (Metric.ball μ₀ 1) := by
    apply tendstoUniformlyOn_tsum hmajorant
    intro k μ hμ
    simpa [derivativeNormTerm] using
      hbound k μ (hboxBound μ hμ)
  rw [EMetric.tendstoUniformlyOn_iff] at huniform ⊢
  intro ε hε
  filter_upwards [tendsto_derivativeBox.eventually (huniform ε hε)] with N hN μ hμ
  simpa [derivativePartial_eq_box] using hN μ hμ

private theorem derivativeNormSeries_locallyUniform
    (he : SA_I13eStatement) (hf : SA_I13fStatement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (r : ℕ) :
    TendstoLocallyUniformly
      (interpolationDerivativeNormPartial q n₁ n₂ r)
      (fun μ => ∑' k : Fin 3 → ℕ, derivativeNormTerm q n₁ n₂ r k μ)
      atTop := by
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro μ₀
  exact ⟨Metric.ball μ₀ 1, Metric.ball_mem_nhds μ₀ zero_lt_one,
    derivativeNormSeries_uniformOn he hf q n₁ n₂ hq hn₁ hn₂ r μ₀⟩

theorem SA_I13gStatement_of_deps
    (he : SA_I13eStatement) (hf : SA_I13fStatement) : SA_I13gStatement := by
  intro q n₁ n₂ hq hn₁ hn₂ r
  constructor
  · intro μ
    obtain ⟨C, hC, hbound⟩ := he q n₁ n₂ hq hn₁ hn₂ ‖μ‖ (norm_nonneg μ) r
    have hmajorant : Summable
        (fun k : Fin 3 → ℕ => C * poissonMajorant ‖μ‖ r k) :=
      (hf ‖μ‖ (norm_nonneg μ) r).mul_left C
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ hmajorant
    intro k
    apply hbound k μ
    intro i
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm μ i)
  · simpa [derivativeNormTerm] using
      derivativeNormSeries_locallyUniform he hf q n₁ n₂ hq hn₁ hn₂ r

end ThLean.W.SA32

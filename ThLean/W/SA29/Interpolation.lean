import ThLean.BP.SA.Basics
import ThLean.BP.SA.Interpolation

noncomputable section
open scoped BigOperators

namespace ThLean.W.SA29
open ThresholdFoundations
open ThLean.BP.SA

private theorem uniformMean_bounds_of_bounds
    {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ)
    (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 := by
  classical
  have hcard : 0 < (Fintype.card A : ℝ) :=
    Nat.cast_pos.2 (Fintype.card_pos_iff.mpr ‹Nonempty A›)
  constructor
  · unfold uniformMean
    exact div_nonneg (Finset.sum_nonneg fun a ha => h0 a) hcard.le
  · unfold uniformMean
    apply (div_le_iff₀ hcard).2
    calc
      ∑ a, f a ≤ ∑ _a : A, (1 : ℝ) := Finset.sum_le_sum fun a ha => h1 a
      _ = (Fintype.card A : ℝ) := by simp
      _ = 1 * (Fintype.card A : ℝ) := by ring

/-- The coefficient bounds and smoothness of the finite interpolation extension,
from the finite-probability, finite-support smoothness, and analytic bridge leaves. -/
theorem SA_I13cStatement_of_deps
    (hF00 : ThLean.BP.SA.SA_F00Statement)
    (hI12d : ThLean.BP.SA.SA_I12dStatement)
    (hI13a : ThLean.BP.SA.SA_I13aStatement) :
    ThLean.BP.SA.SA_I13cStatement := by
  intro q n₁ n₂ hq h₁ h₂
  constructor
  · intro k
    letI : Nonempty (Fin (n₁ + n₂) × Fin (n₁ + n₂)) :=
      ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    letI : Nonempty (Fin n₁ × Fin n₁) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    letI : Nonempty (Fin n₂ × Fin n₂) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    let A₀ := Fin (k 0) → Fin (n₁ + n₂) × Fin (n₁ + n₂)
    let A₁ := Fin (k 1) → Fin n₁ × Fin n₁
    let A₂ := Fin (k 2) → Fin n₂ × Fin n₂
    have hinner (x₀ : A₀) (x₁ : A₁) :
        0 ≤ uniformMean (fun x₂ : A₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂))) ∧
        uniformMean (fun x₂ : A₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂))) ≤ 1 := by
      have hp := hF00.1 (A := A₂)
        (fun x₂ => Colorable q (mixedGraph x₀ x₁ x₂))
      exact ⟨by simpa [uniformProb] using hp.1,
        by simpa [uniformProb] using hp.2.1⟩
    have hmiddle (x₀ : A₀) :
        0 ≤ uniformMean (fun x₁ : A₁ => uniformMean (fun x₂ : A₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂)))) ∧
        uniformMean (fun x₁ : A₁ => uniformMean (fun x₂ : A₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂)))) ≤ 1 := by
      apply uniformMean_bounds_of_bounds
      · intro x₁
        exact (hinner x₀ x₁).1
      · intro x₁
        exact (hinner x₀ x₁).2
    have houter :
        0 ≤ uniformMean (fun x₀ : A₀ => uniformMean (fun x₁ : A₁ =>
          uniformMean (fun x₂ : A₂ =>
            indicator (Colorable q (mixedGraph x₀ x₁ x₂))))) ∧
        uniformMean (fun x₀ : A₀ => uniformMean (fun x₁ : A₁ =>
          uniformMean (fun x₂ : A₂ =>
            indicator (Colorable q (mixedGraph x₀ x₁ x₂))))) ≤ 1 := by
      apply uniformMean_bounds_of_bounds
      · intro x₀
        exact (hmiddle x₀).1
      · intro x₀
        exact (hmiddle x₀).2
    simpa [interpolationCoefficient, A₀, A₁, A₂] using houter
  · intro r
    have hrate : ContDiff ℝ r
        (fun μ : Fin 3 → ℝ => markRate n₁ n₂ μ) := by
      apply contDiff_pi.2
      intro d
      cases d with
      | inl e =>
          change ContDiff ℝ r (fun μ : Fin 3 → ℝ =>
            μ 0 / (((n₁ + n₂ : ℕ) : ℝ) ^ 2))
          fun_prop
      | inr e =>
          cases e with
          | inl e =>
              change ContDiff ℝ r (fun μ : Fin 3 → ℝ =>
                μ 1 / ((n₁ : ℝ) ^ 2))
              fun_prop
          | inr e =>
              change ContDiff ℝ r (fun μ : Fin 3 → ℝ =>
                μ 2 / ((n₂ : ℝ) ^ 2))
              fun_prop
    have hfinite : ContDiff ℝ r
        (fun μ : Fin 3 → ℝ => finiteChiBar q n₁ n₂ μ) := by
      have hsupport := hI12d (D := TaggedMark n₁ n₂)
        (F := fun T => indicator (Colorable q (supportGraph T))) r
      have hcomp := hsupport.comp hrate
      simpa [finiteChiBar, chiSupport, supportMean, markRate,
        Function.comp_def,
        ThLean.BP.SA.supportGraph] using hcomp
    have heq : (fun μ : Fin 3 → ℝ => chiBar q n₁ n₂ μ) =
        (fun μ => finiteChiBar q n₁ n₂ μ) := by
      funext μ
      exact (hI13a q n₁ n₂ (by omega) (by omega) (by omega) μ).2
    change ContDiff ℝ r (fun μ : Fin 3 → ℝ => chiBar q n₁ n₂ μ)
    rw [heq]
    exact hfinite

end ThLean.W.SA29

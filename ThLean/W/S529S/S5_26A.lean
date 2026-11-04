module

public import ThLean.W.S529S.Averages
public import ThLean.W.S529.S5_26A

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S529S
open ThresholdFoundations ThLean.BP.S5

/-- Integrate the fixed-set discrepancy bound and average over uniform identified sets. -/
theorem early_integral_assembly_of_deps
    (h20 : S5_20Statement) (h21 : S5_21Statement) (h22 : S5_22Statement)
    (h24 : S5_24Statement) (h25 : S5_25Statement) :
    ThLean.Contrib.S529.S5_26AEarlyIntegralAssemblyStatement := by
  intro q N D k hq hN hD h4 hk
  have hp := h22 q N D hq hN hD h4
  have hN3 : 3 ≤ N := by omega
  have hND : 2 ≤ N - D := hp.2.2.2.1
  have hr : 0 < lowEdgeRate N := hp.2.2.2.2.1
  have hT : 0 ≤ lowTimeCap q N := hp.2.2.2.2.2.2.1.le
  have hm := hp.2.2.2.2.2.2.2.2.2.2
  have : Nonempty (UniformSubset (Fin N) D) := by
    have hlt : D < N := by omega
    exact ⟨⟨Finset.Iio (⟨D, hlt⟩ : Fin N), by simp⟩⟩
  let T := lowTimeCap q N
  let F := fun (Z : UniformSubset (Fin N) D) (s : ℝ) =>
    poissonGraphMean s (fun G : MGraph (Fin N) =>
      indicator (Colorable q G ∧ ¬ Colorable q (identify G Z.val)))
  let inside := fun s : ℝ => lowEdgeRate N * (D.choose 2 : ℝ) * s
  let tail := fun s : ℝ =>
    ∑' j : ℕ, if k < j then poissonWeight (D * neighborMean N D s) j else 0
  let main := fun (Z : UniformSubset (Fin N) D) (s : ℝ) =>
    (D : ℝ)^k * addedFailure (V := {v : Fin N // v ∉ Z.val}) q
      (lowEdgeRate N * s) (neighborMean N D s)
  have hi : IntegrableOn inside (Set.Icc 0 T) :=
    (show Continuous inside by dsimp [inside]; fun_prop).integrableOn_Icc
  have ht : IntegrableOn tail (Set.Icc 0 T) :=
    (h24 q N D k hq hN hD h4 hk).2.2.1
  have hmain (Z : UniformSubset (Fin N) D) :
      IntegrableOn (main Z) (Set.Icc 0 T) := (h25 q N D k hq hN hD h4 Z).1
  have hii : IntervalIntegrable inside volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hi
  have hti : IntervalIntegrable tail volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 ht
  have hmi (Z : UniformSubset (Fin N) D) :
      IntervalIntegrable (main Z) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 (hmain Z)
  have hfixed (Z : UniformSubset (Fin N) D) :
      IntervalIntegrable (F Z) volume 0 T ∧
      (∫ s in (0 : ℝ)..T, F Z s) ≤
        (∫ s in (0 : ℝ)..T, inside s) +
        (∫ s in (0 : ℝ)..T, tail s) + (∫ s in (0 : ℝ)..T, main Z s) := by
    have hZne : Z.val.Nonempty := Finset.card_pos.mp (by omega)
    have hZout : 2 ≤ N - Z.val.card := by simpa only [Z.property] using hND
    have hspl := h20 q N hq hN3 Z.val hZne hZout
    have hcomp (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
        F Z s ≤ inside s + tail s + main Z s := by
      have hsplit : F Z s ≤ inside s +
          addedFailure (V := {v : Fin N // v ∉ Z.val}) q
            (lowEdgeRate N * s) (D * neighborMean N D s) := by
        simpa only [F, inside, Z.property] using hspl.1 s hs.1
      have hb := fun j => blockingMean_range (V := {v : Fin N // v ∉ Z.val})
        q (mul_nonneg hr.le hs.1) j
      have htilt := (h21 D k hD (neighborMean N D s) (hm s hs.1 hs.2).1).2
        (blockingMean (V := {v : Fin N // v ∉ Z.val}) q (lowEdgeRate N * s)) hb
      have htilt' :
          addedFailure (V := {v : Fin N // v ∉ Z.val}) q
            (lowEdgeRate N * s) (D * neighborMean N D s) ≤ main Z s + tail s := by
        exact htilt.2.2
      linarith
    have hF0 (s : ℝ) (hs : 0 ≤ s) : 0 ≤ F Z s :=
      graphMean_nonneg hs (fun _ => (indicator_range _).1)
    have hFi : IntegrableOn (F Z) (Set.Icc 0 T) := by
      apply ((hi.add ht).add (hmain Z)).mono_nonneg
        (ThLean.W.S523S.poissonGraphMean_measurable _).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hF0 s hs.1
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hcomp s hs
    have hFii : IntervalIntegrable (F Z) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hFi
    refine ⟨hFii, ?_⟩
    have hle := intervalIntegral.integral_mono_on hT hFii
      ((hii.add hti).add (hmi Z)) hcomp
    rw [intervalIntegral.integral_add (hii.add hti) (hmi Z),
      intervalIntegral.integral_add hii hti] at hle
    exact hle
  have havg : (∫ s in (0 : ℝ)..T, discrepancy q N D s) =
      uniformMean (fun Z : UniformSubset (Fin N) D => ∫ s in (0 : ℝ)..T, F Z s) := by
    calc
      _ = ∫ s in (0 : ℝ)..T, uniformMean (fun Z => F Z s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hT] at hs
        exact discrepancy_average q N D hs.1
      _ = _ := integral_uniformMean F 0 T (fun Z => (hfixed Z).1)
  rw [havg]
  calc
    _ ≤ uniformMean (fun Z : UniformSubset (Fin N) D =>
        (∫ s in (0 : ℝ)..T, inside s) + (∫ s in (0 : ℝ)..T, tail s) +
          (∫ s in (0 : ℝ)..T, main Z s)) :=
      uniformMean_mono (fun Z => (hfixed Z).2)
    _ = _ := by rw [uniformMean_add, uniformMean_const]

/-- The early-time identification estimate follows from the Poisson comparison,
tail bounds, and averaged integral estimate. -/
theorem S5_26AStatement_of_deps
    (h20 : S5_20Statement) (h21 : S5_21Statement)
    (h22 : S5_22Statement) (h23 : S5_23Statement)
    (h24 : S5_24Statement) (h25 : S5_25Statement)
    (hE08 : S5_E08Statement) : S5_26AStatement :=
  ThLean.W.S529.S5_26AStatement_of_early_assembly h20 h21 h22 h23 h24 h25 hE08
    (early_integral_assembly_of_deps h20 h21 h22 h24 h25)

example (h20 : S5_20Statement) (h21 : S5_21Statement)
    (h22 : S5_22Statement) (h23 : S5_23Statement)
    (h24 : S5_24Statement) (h25 : S5_25Statement)
    (hE08 : S5_E08Statement) : ThLean.BP.S5.S5_26AStatement :=
  S5_26AStatement_of_deps h20 h21 h22 h23 h24 h25 hE08

end ThLean.W.S529S

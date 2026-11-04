module

public import ThLean.BP.S5.Identification
public import ThLean.Contrib.S529.EarlyAssembly

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S529
open ThLean.BP.S5 ThresholdFoundations

theorem S5_26AStatement_of_early_assembly
    (h20 : S5_20Statement) (h21 : S5_21Statement)
    (h22 : S5_22Statement) (h23 : S5_23Statement)
    (h24 : S5_24Statement) (h25 : S5_25Statement)
    (hE08 : S5_E08Statement)
    (hcore : ThLean.Contrib.S529.S5_26AEarlyIntegralAssemblyStatement) :
    S5_26AStatement := by
  intro q N D k hq hN hD h4 hk
  have h22q := h22 q N D hq hN hD h4
  have hN2 : 2 ≤ N := by omega
  have hDN : D ≤ N := h22q.2.2.1
  have h23q := h23 q N D hq hN2 hD hDN
  have h24q := h24 q N D k hq hN hD h4 hk
  have hcoreq := hcore q N D k hq hN hD h4 hk
  have hsubset : Nonempty (UniformSubset (Fin N) D) := by
    have hlt : D < N := by omega
    refine ⟨⟨Finset.Iio (⟨D, hlt⟩ : Fin N), ?_⟩⟩
    simp
  have hmain_each : ∀ Z : UniformSubset (Fin N) D,
      (∫ s in (0 : ℝ)..lowTimeCap q N,
        (D : ℝ)^k * addedFailure (V := {v : Fin N // v ∉ Z.val}) q
          (lowEdgeRate N * s) (neighborMean N D s)) ≤
        2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ)^k := by
    intro Z
    exact ((h25 q N D k hq hN hD h4 Z).2.1).trans
      (h25 q N D k hq hN hD h4 Z).2.2
  have hmain_avg : uniformMean (fun Z : UniformSubset (Fin N) D =>
      ∫ s in (0 : ℝ)..lowTimeCap q N,
        (D : ℝ)^k * addedFailure (V := {v : Fin N // v ∉ Z.val}) q
          (lowEdgeRate N * s) (neighborMean N D s)) ≤
      2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ)^k := by
    have hcard : 0 < (Fintype.card (UniformSubset (Fin N) D) : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr hsubset
    unfold uniformMean
    apply (div_le_iff₀ hcard).2
    calc
      (∑ Z : UniformSubset (Fin N) D,
          ∫ s in (0 : ℝ)..lowTimeCap q N,
            (D : ℝ)^k * addedFailure (V := {v : Fin N // v ∉ Z.val}) q
              (lowEdgeRate N * s) (neighborMean N D s)) ≤
          ∑ _Z : UniformSubset (Fin N) D,
            2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ)^k :=
        Finset.sum_le_sum fun Z _ => hmain_each Z
      _ = (2 * (Real.exp (lowMeanBound q) - 1) * (D : ℝ)^k) *
          (Fintype.card (UniformSubset (Fin N) D) : ℝ) := by
        simp
        ring
  have htail := h24q.2.2.2
  have hins := h23q.2.2
  have hbound := hcoreq.trans (add_le_add (add_le_add hins htail) hmain_avg)
  linarith

theorem S5_26AStatement_of_deps
    (h20 : S5_20Statement) (h21 : S5_21Statement)
    (h22 : S5_22Statement) (h23 : S5_23Statement)
    (h24 : S5_24Statement) (h25 : S5_25Statement)
    (hE08 : S5_E08Statement)
    (hcore : ThLean.Contrib.S529.S5_26AEarlyIntegralAssemblyStatement) :
    S5_26AStatement :=
  S5_26AStatement_of_early_assembly h20 h21 h22 h23 h24 h25 hE08 hcore

end ThLean.W.S529

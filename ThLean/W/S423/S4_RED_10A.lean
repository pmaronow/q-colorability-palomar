module

public import ThLean.BP.S4.Bridges

@[expose] public section

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S423

open ThresholdFoundations
open ThLean.BP.S4

theorem S4_RED_10AStatement_of_deps
    (hred : S4_RED_05Statement)
    (hbridge : S4_BRIDGE_03AStatement)
    (hlife : PreLifetimeStatement.{0}) :
    S4_RED_10AStatement := by
  intro q n hq hn L U h hLh hhU G e hG hc hfail
  have hpos : 1 ≤ h := by omega
  let b : ℕ := U + 1 - h
  have hb1 : 1 ≤ b := by dsimp [b]; omega
  have hbwidth : b ≤ U - L := by
    dsimp [b]
    apply (Nat.le_sub_iff_add_le (Nat.le_trans (Nat.le_of_lt hLh) hhU)).2
    omega
  have hn2 : 2 ≤ Fintype.card (Fin n) := by
    simpa using (show 2 ≤ n by omega)
  have hpre := (hlife (V := Fin n) q hq hn2).1 G hG
  have htr := hpre.2.1 b
  have hrge : 1 ≤ truncatedLifetime q b G := hpre.2.2.2.1 hc b hb1
  have hredG := hred q n hq hn h U hpos hhU G hG
  have hweight := (hredG.2.2.2.2 hc).1
  have hweight' :
      1 ≤ 2 * truncatedLifetime q b G - 1 := by
    simpa [b, deletionWeight, hc] using hweight
  have hfinite := hbridge q n hq hn G hG
  have hrreal : truncatedLifetime q b G ≤ lifetimeReal q G := by
    have hh := (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hfinite.1)).mp htr.2.1
    simpa [lifetimeReal] using hh
  have hwidthReal : (b : ℝ) ≤ (U : ℝ) - L := by
    rw [← Nat.cast_sub (Nat.le_trans (Nat.le_of_lt hLh) hhU)]
    exact_mod_cast hbwidth
  have hrwidth : truncatedLifetime q b G ≤ (U : ℝ) - L :=
    le_trans htr.2.2 hwidthReal
  have hrmin : truncatedLifetime q b G ≤ min ((U : ℝ) - L) (lifetimeReal q G) :=
    le_min hrwidth hrreal
  have hhReal : 0 ≤ (h : ℝ) := Nat.cast_nonneg _
  have hUReal : 0 ≤ (U : ℝ) := Nat.cast_nonneg _
  have hhCast : (h : ℝ) ≤ (U : ℝ) := by exact_mod_cast hhU
  have hprod : (h : ℝ) * truncatedLifetime q b G ≤
      (U : ℝ) * min ((U : ℝ) - L) (lifetimeReal q G) :=
    mul_le_mul hhCast hrmin htr.1 hUReal
  refine ⟨by omega, ?_, ?_, ?_⟩
  · simpa [b] using hbwidth
  · have hweight0 : 0 ≤ 2 * truncatedLifetime q b G - 1 := by linarith
    exact mul_nonneg hhReal hweight0
  · nlinarith [hprod]

end ThLean.W.S423

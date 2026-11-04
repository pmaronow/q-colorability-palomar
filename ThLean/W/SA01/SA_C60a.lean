module

public import ThLean.BP.SA.Convergence

@[expose] public section

noncomputable section
open scoped BigOperators Topology ENNReal
namespace ThLean.W.SA01
open ThresholdFoundations

/-- Normalized lower quantiles lie between zero and the density cap. -/
theorem SA_C60aStatement_of_deps
    (hF01 : ThLean.BP.SA.SA_F01Statement)
    (hPre : ThresholdFoundations.PreQuantileStatement) :
    ThLean.BP.SA.SA_C60aStatement := by
  intro q hq Λ η hΛ hη hηhalf n hn
  have hn2 : 2 ≤ n := by omega
  have hΛpos := (hF01 q hq).2.2 Λ hΛ |>.1
  have hxnonneg : 0 ≤ Λ * (n : ℝ) := mul_nonneg hΛpos.le (Nat.cast_nonneg n)
  have hquant := hPre q n (cap Λ n) hq hn2 η hη hηhalf
  have hLU : lowerLocation q Λ η n ≤ upperLocation q Λ η n := by
    simpa [lowerLocation, upperLocation] using hquant.1
  have hUcap : upperLocation q Λ η n ≤ cap Λ n := by
    simpa [lowerLocation, upperLocation] using hquant.2.1
  have hLcap : lowerLocation q Λ η n ≤ cap Λ n := le_trans hLU hUcap
  have hcap : (cap Λ n : ℝ) ≤ Λ * (n : ℝ) := by
    exact Nat.floor_le hxnonneg
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    apply (div_le_iff₀ hnpos).2
    exact le_trans (by exact_mod_cast hLcap) hcap

end ThLean.W.SA01

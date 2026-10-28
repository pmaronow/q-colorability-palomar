import ThLean.BP.SA.Convergence
import ThLean.BP.SA.Alternatives
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ThLean.BP.SA
open ThresholdFoundations

/-- Owned interface lem:conv-interp, from P5-I17. -/
theorem ConvInterp_of_SA (h : SA_I17Statement) : ThresholdFoundations.ConvInterpStatement := by
  intro q hq n₁ n₂ h₁ h₂ c hc
  exact h q n₁ n₂ (by omega) h₁ h₂ c hc

/-- Owned interface lem:conv-quantile, including the common density-independent cutoff. -/
theorem ConvQuantile_of_SA (h20 : SA_Q20Statement) (h22 : SA_Q22Statement)
    (hcentre : PreCentreStatement) : ThresholdFoundations.ConvQuantileStatement := by
  constructor
  · intro q n hq hn c hc
    exact (h20 q n (by omega) (by omega) c hc).2.2.2
  · intro q hq Λ hΛ η hη hhalf
    have hev := (hcentre q hq Λ hΛ η hη hhalf).2.1 (gamma q + 1) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨max (2 * q) N, le_max_left _ _, ?_⟩
    intro n hn c hc hcΛ
    have hqn : 2 * q ≤ n := le_trans (le_max_left _ _) hn
    have hcap := (hN n (le_trans (le_max_right _ _) hn)).2.2
    exact ⟨h22.1 q n hq hqn Λ η c hΛ hη hhalf hc hcΛ,
      h22.2 q n hq hqn Λ η c hΛ hη hhalf hc hcΛ hcap⟩

/-- Owned interface lem:conv-superadd, from P5-Q28. -/
theorem ConvSuperadd_of_SA (h : SA_Q28Statement) : ThresholdFoundations.ConvSuperaddStatement := by
  intro q hq Λ hΛ δ hδ η hη hη₀ K N hK hw
  exact h q hq Λ η K δ N hΛ hδ hη hη₀ ⟨hK, hw⟩

/-- Owned interface lem:conv-tree; P5-T38 also permits zero errors. -/
theorem ConvTree_of_SA (h : SA_T38Statement) : ThresholdFoundations.ConvTreeStatement := by
  intro u₀ hu₀ g hg hanti hsum s₀ ξ hcmp hb
  obtain ⟨B, hB⟩ := hb
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (ξ s₀)) (hB s₀ le_rfl)
  exact h u₀ g ⟨hu₀, fun u hu => (hg u hu).le, hanti, hsum⟩ ξ s₀ B hB0 hB hcmp

/-- Owned interface lem:conv-transfer, with exact finite binomial mixtures. -/
theorem ConvTransfer_of_SA (h52 : SA_X52Statement) (h53 : SA_X53Statement)
    (h54 : SA_X54Statement) (h55 : SA_X55Statement) (hsums : SA_X55aStatement) :
    ThresholdFoundations.ConvTransferStatement := by
  refine ⟨h52, ?_⟩
  intro q n hq hn
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab hb
    exact h53 q n a b (by omega) hn hab hb
  · intro p hp hp1
    exact (h54 q n (by omega) hn p hp hp1).1
  · intro m p hm hp hp1
    have hh := h55 q n m (by omega) hn hm p hp hp1
    obtain ⟨hle, hlt⟩ := hsums (n.choose 2) m hm p
    rwa [hle, hlt] at hh

/-- Owned interface thm:red-convergence, with one witness for every conclusion. -/
theorem RedConvergence_of_SA (h : SA_C66Statement) : ThresholdFoundations.RedConvergenceStatement := by
  intro q hq Λ hΛ δ hδ hw
  apply h q hq Λ δ hΛ hδ
  intro η hη hη₀
  obtain ⟨K, hK, N, _, hbound⟩ := hw η hη hη₀
  refine ⟨K, N, hK, ?_⟩
  intro n hn
  exact hbound n (le_trans (le_max_right _ _) hn)
end ThLean.BP.SA

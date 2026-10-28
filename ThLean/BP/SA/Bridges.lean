import ThLean.BP.SA.Analytic
import ThLean.BP.SA.Interfaces
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ThLean.BP.SA
open ThresholdFoundations

/-- B17, from the loop splitting and one-vertex nodes. -/
theorem RhoProcess_of_SA (h20 : SA_Q20Statement) (h13 : SA_I13bStatement) :
    ThresholdFoundations.RhoProcessStatement := by
  constructor
  · intro q n hq hn c hc
    exact (h20 q n (by omega) hn c hc).2.2.2
  · intro q hq c hc
    exact h13.2.2 q (by omega) c hc

/-- B18, exact frozen factorial-series interpolation including its derivative. -/
theorem InterpolationBridge_of_SA (h13 : SA_I13Statement) (h13c : SA_I13cStatement)
    (h16 : SA_I16Statement) (h16d : SA_I16dStatement) (h17 : SA_I17Statement)
    (hnormal : SA_I13gStatement) :
    ThresholdFoundations.InterpolationBridgeStatement := by
  intro q n₁ n₂ hq h₁ h₂
  have hq1 : 1 ≤ q := by omega
  have hcoeff := h13c q n₁ n₂ hq1 h₁ h₂
  refine ⟨hcoeff.1, ?_, hnormal q n₁ n₂ hq1 h₁ h₂, hcoeff.2, ?_, ?_, ?_⟩
  · intro μ
    exact (h13.1 q n₁ n₂ hq1 h₁ h₂ μ).1
  · intro μ _
    exact (h13.1 q n₁ n₂ hq1 h₁ h₂ μ).2
  · intro c θ hc hθ hθc
    have hI : θ ∈ Set.Icc 0 c := ⟨hθ.le, hθc.le⟩
    have hd := h16.2.1 q n₁ n₂ hq1 h₁ h₂ c hc θ hI
    have heq : chi q n₁ n₂ c = finiteChi q n₁ n₂ c := by
      funext t
      exact (h13.1 q n₁ n₂ hq1 h₁ h₂ (interpolationMeans n₁ n₂ c t)).2
    rw [← heq, ← (h16d q n₁ n₂ hq1 h₁ h₂ c hc.le θ hI).2] at hd
    refine ⟨hd, ?_⟩
    rw [(h16d q n₁ n₂ hq1 h₁ h₂ c hc.le θ hI).2]
    exact (h16.2.2 q n₁ n₂ hq1 h₁ h₂).2 c hc.le θ hI
  · intro c hc
    obtain ⟨h0, hc'⟩ := h13.2.1 q n₁ n₂ hq1 h₁ h₂ c hc
    have heq : chi q n₁ n₂ c = finiteChi q n₁ n₂ c := by
      funext t
      exact (h13.1 q n₁ n₂ hq1 h₁ h₂ (interpolationMeans n₁ n₂ c t)).2
    rw [heq]
    exact ⟨h0, hc', h17 q n₁ n₂ hq1 h₁ h₂ c hc⟩

/-- B19, joint colorability law, exact birthday product, and its uniform lower bound. -/
theorem DistinctTransfer_of_SA (h50 : SA_X50bStatement) (h50c : SA_X50cStatement)
    (h51 : SA_X51Statement) : ThresholdFoundations.DistinctTransferStatement := by
  refine ⟨?_, h50, ?_⟩
  · intro q n m hq hn hm
    exact h50c q n m (by omega) hn hm
  · intro Λ hΛ
    obtain ⟨N, hN, hlarge⟩ := h51.2 Λ hΛ.le
    filter_upwards [eventually_ge_atTop N] with n hn
    intro m hm
    obtain ⟨ha, hb⟩ := hlarge n hn
    exact (h51.1 Λ n hΛ.le (hN.trans hn) ha hb m hm).2

/-- B20 is exactly the complete frozen transfer contract. -/
theorem BinomialTransfer_of_SA (h52 : SA_X52Statement) (h53 : SA_X53Statement)
    (h54 : SA_X54Statement) (h55 : SA_X55Statement) (hsums : SA_X55aStatement) :
    ThresholdFoundations.BinomialTransferStatement :=
  ConvTransfer_of_SA h52 h53 h54 h55 hsums

/-- B21, including floor agreement and threshold uniqueness. -/
theorem EventualDomain_of_SA (ha : SA_X59aStatement) (hb : SA_X59bStatement)
    (hu : SA_C67Statement) : ThresholdFoundations.EventualDomainStatement := by
  refine ⟨ha, hb, ?_⟩
  intro q α β hq hα hβ hαlim hβlim
  exact hu q hq α β (by linarith [hα.1]) (by linarith [hβ.1]) hαlim hβlim
end ThLean.BP.SA

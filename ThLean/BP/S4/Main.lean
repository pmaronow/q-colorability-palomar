import ThLean.BP.S4.Window

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S4
open ThresholdFoundations

/-- Section 7's exact epsilon interface from its analytic subleaves. -/
theorem EpsilonAdmissible_of_S4 (hr : S4_PAR_03Statement) (hs : S4_PAR_05Statement)
    (hl : S4_PAR_06Statement) : EpsilonAdmissibleStatement := by
  exact ⟨⟨fun n _ => hr.1 n, fun n m _ hnm => hr.2 n m hnm, hs⟩, hl.1, hl.2.1⟩

private theorem window_bound_of_precise (hw : S4_AS_02Statement) (hp : S4_PAR_01AStatement)
    (q : ℕ) (hq : 3 ≤ q) (Λ : ℝ) (hΛ : gamma q+1 < Λ) : WindowBound q Λ epsilon := by
  intro η hη hη0
  obtain ⟨N,hN,hw⟩ := hw q hq Λ hΛ
  exact ⟨6*Λ/η^2, (((hp q hq).2.2.2 Λ hΛ).2.2.2.1 η hη hη0).2,
    N, (le_max_right _ _).trans hN, fun n hn => hw n hn η hη hη0⟩

/-- P2-AS-03, one convergence witness for all four conclusions; thm:intro-main. -/
def S4_AS_03Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ α : ℝ, α ∈ Set.Icc (1/2 : ℝ) (gamma q) ∧
    QuantileLimits q (capDensity q) α ∧ ProcessLimits q α ∧ SimpleLimits q α ∧ BinomialLimits q α

theorem S4_AS_03_assembly (hc : RedConvergenceStatement) (hw : S4_AS_02Statement)
    (hp : S4_PAR_01Statement) (he : S4_PAR_03Statement) (hs : S4_PAR_05Statement)
    (hl : S4_PAR_06Statement) : S4_AS_03Statement := by
  intro q hq
  exact hc q hq (capDensity q) (hp.2 q hq) epsilon
    (EpsilonAdmissible_of_S4 he hs hl).1
    (window_bound_of_precise hw hp.1 q hq _ (hp.2 q hq))

private theorem public_threshold (hp : PublicModelsStatement) (q : ℕ) (α : ℝ)
    (ha : α ∈ Set.Icc (1/2 : ℝ) (gamma q)) (hs : SimpleLimits q α) (hb : BinomialLimits q α) :
    ThresholdChallenge.ThresholdStatement q α := by
  rcases hp with ⟨hproc,hsimple,hbin,hsparse,hgamma,hrange⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hgamma] using ha
  · intro c hc hca
    simpa only [hsimple] using hs.1 c hc hca
  · intro c hac
    simpa only [hsimple] using hs.2 c hac
  · intro d hd hda
    simpa only [hsparse] using hb.1 d hd hda
  · intro d had
    simpa only [hsparse] using hb.2 d had

private theorem public_window (hp : WindowProbabilityStatement) (q : ℕ) (hq : 3 ≤ q)
    (α : ℝ) (hw : ConfidenceWindow q α) : ThresholdChallenge.WindowStatement q α := by
  intro η hη hη1
  obtain ⟨C,hC,N,hN,m,hm,hw⟩ := hw η hη hη1
  refine ⟨C,hC,N,hN,m,hm,?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by have := (le_max_left 3 (2*q)).trans (hN.trans hn); omega
  rw [(hp q n hq hn2 _ _).1]
  exact hw n hn

/-- P2-AS-04, Theorem 1.1 in the frozen public model. -/
def S4_AS_04Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ α : ℝ, ThresholdChallenge.ThresholdStatement q α

theorem S4_AS_04_assembly (hc : S4_AS_03Statement) (hp : PublicModelsStatement) :
    S4_AS_04Statement := by
  intro q hq
  obtain ⟨α,ha,hqnt,hproc,hs,hb⟩ := hc q hq
  exact ⟨α,public_threshold hp q α ha hs hb⟩

private theorem limits_unique (F : ℝ → ℕ → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαlo : ∀ c : ℝ, 0 ≤ c → c < α → Tendsto (F c) atTop (𝓝 1))
    (hαhi : ∀ c : ℝ, α < c → Tendsto (F c) atTop (𝓝 0))
    (hβlo : ∀ c : ℝ, 0 ≤ c → c < β → Tendsto (F c) atTop (𝓝 1))
    (hβhi : ∀ c : ℝ, β < c → Tendsto (F c) atTop (𝓝 0)) : α = β := by
  rcases lt_trichotomy α β with hlt | heq | hgt
  · have he : (0 : ℝ) = 1 := tendsto_nhds_unique
      (hαhi ((α+β)/2) (by linarith)) (hβlo ((α+β)/2) (by linarith) (by linarith))
    norm_num at he
  · exact heq
  · have he : (0 : ℝ) = 1 := tendsto_nhds_unique
      (hβhi ((α+β)/2) (by linarith)) (hαlo ((α+β)/2) (by linarith) (by linarith))
    norm_num at he

/-- P2-AS-07, uniqueness for both internal threshold laws; thm:red-convergence. -/
def S4_AS_07Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
    (SimpleLimits q α → SimpleLimits q β → α=β) ∧
    (ProcessLimits q α → ProcessLimits q β → α=β)

theorem S4_AS_07_assembly : S4_AS_07Statement := by
  intro q hq α β hα hβ
  constructor
  · intro ha hb
    exact limits_unique (fun c n => simpleProbability (V := Fin n) q (Nat.floor (c*n)))
      α β hα hβ ha.1 ha.2 hb.1 hb.2
  · intro ha hb
    exact limits_unique (fun c n => processSurvival (V := Fin n) q (Nat.floor (c*n)))
      α β hα hβ ha.1 ha.2 hb.1 hb.2

/-- P2-AS-08, a joint witness and uniqueness for any other threshold witness. -/
def S4_AS_08Statement : Prop :=
  (∀ q : ℕ, 3 ≤ q → ∃ α : ℝ, α ∈ Set.Icc (1/2 : ℝ) (gamma q) ∧
    SimpleLimits q α ∧ BinomialLimits q α ∧ ConfidenceWindow q α) ∧
  (∀ q : ℕ, 3 ≤ q → ∀ α : ℝ, α ∈ Set.Icc (1/2 : ℝ) (gamma q) →
    SimpleLimits q α → BinomialLimits q α → ConfidenceWindow q α)

theorem S4_AS_08_assembly (hc : S4_AS_03Statement) (hw : S4_AS_02Statement)
    (hconf : S4_AS_06Statement) (hp : S4_PAR_01Statement) : S4_AS_08Statement := by
  have hex : ∀ q : ℕ, 3 ≤ q → ∃ α : ℝ, α ∈ Set.Icc (1/2 : ℝ) (gamma q) ∧
      SimpleLimits q α ∧ BinomialLimits q α ∧ ConfidenceWindow q α := by
    intro q hq
    obtain ⟨α,ha,hqnt,hproc,hs,hb⟩ := hc q hq
    refine ⟨α,ha,hs,hb,?_⟩
    exact hconf q hq _ (hp.2 q hq) α hqnt
      (window_bound_of_precise hw hp.1 q hq _ (hp.2 q hq))
  refine ⟨hex, ?_⟩
  intro q hq α ha hs hb
  obtain ⟨β,hβ,hβs,hβb,hβw⟩ := hex q hq
  have heq := (S4_AS_07_assembly q hq α β (by linarith [ha.1]) (by linarith [hβ.1])).1 hs hβs
  simpa only [heq] using hβw

/-- Final public theorem from the joint internal witness and the two public-model bridges. -/
theorem MainChallenge_of_S4 (hm : S4_AS_08Statement) (hp : PublicModelsStatement)
    (hw : WindowProbabilityStatement) : ThresholdChallenge.MainStatement := by
  intro q hq
  obtain ⟨α,ha,hs,hb,hconf⟩ := hm.1 q hq
  exact ⟨α,public_threshold hp q α ha hs hb,public_window hw q hq α hconf⟩

/-- The frozen final contract, proved from Section 4/7 nodes and its explicit section inputs. -/
theorem MainFromSections_of_S4 (hp : S4_PAR_01Statement) (hs : S4_PAR_06Statement)
    (hm : S4_RED_13AStatement) (hb : S4_BRIDGE_01Statement) (hw : S4_BRIDGE_02Statement) :
    MainFromSections := by
  intro hqnt hcentre hsplit hlow hhigh hepsilon hconv hpublic hpublicWindow
  have hrestrict := S4_AS_01_assembly hb.2.1 hb.2.2 hm
  have hwidth := S4_AS_02_assembly hlow hhigh hsplit hrestrict hp.1
  have hmass := S4_AS_05_assembly hqnt hp.1 hb.1
  have hconfidence := S4_AS_06_assembly hp.1 hs hcentre hmass hw
  intro q hq
  have hwb := window_bound_of_precise hwidth hp.1 q hq (capDensity q) (hp.2 q hq)
  obtain ⟨α,ha,hql,hproc,hsl,hbl⟩ :=
    hconv q hq (capDensity q) (hp.2 q hq) epsilon hepsilon.1 hwb
  have hcw := hconfidence q hq (capDensity q) (hp.2 q hq) α hql hwb
  exact ⟨α, public_threshold hpublic q α ha hsl hbl, public_window hpublicWindow q hq α hcw⟩

end ThLean.BP.S4

module

public import ThLean.BP.S4.Reduction

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S4
open ThresholdFoundations

private theorem moment_eq (q n L U : ℕ) (a : ℝ) :
    cappedMoment q n L U a = truncatedTerminalLifetime (V := Fin n) q L U a := rfl

private theorem deletion_moment_eq (q n L U : ℕ) :
    deletionMoment q n L U = terminalWindow (V := Fin n) q L U
      (fun m G _ => ((m+1 : ℕ) : ℝ)*(2*truncatedLifetime q (U-m) G-1)) := by
  unfold deletionMoment terminalReal terminalWindow terminalStep
  have h : ∀ m : ℕ, U+1-(m+1) = U-m := by omega
  simp only [h]

/-- lem:red-deletion, exported at the exact frozen interface type. -/
theorem RedDeletion_of_S4 (hv : S4_RED_11Statement) (hm : S4_RED_13AStatement) :
    RedDeletionStatement := by
  intro q hq Λ hΛ η hη hη0 n hn
  have hLU := (hm q hq Λ hΛ n hn η hη hη0).1
  simpa only [deletion_moment_eq, moment_eq, window] using hv q n hq hn _ _ hLU

/-- lem:red-varlower, exported at the exact frozen interface type. -/
theorem RedVarlower_of_S4 (h : S4_RED_13Statement) : RedVarlowerStatement := by
  intro q hq Λ hΛ η hη hη0 n hn
  exact h q hq Λ hΛ n hn η hη hη0

/-- prop:red-window, exported at the exact frozen interface type. -/
theorem RedWindow_of_S4 (h : S4_RED_14Statement) : RedWindowStatement := by
  intro q hq Λ hΛ η hη hη0 n hn K hK hmoment
  exact h q hq Λ hΛ n hn η hη hη0 K hK hmoment

/-- prop:red-split, with explicit real/extended event transport. -/
theorem RedSplit_of_S4 (h : S4_RED_17Statement) (hb : S4_BRIDGE_03BStatement)
    (hm : S4_RED_13AStatement) : RedSplitStatement := by
  intro q hq Λ hΛ η hη hη0 n hn
  dsimp only
  intro hlow hhigh
  have hLU := (hm q hq Λ hΛ n hn η hη hη0).1
  have hy : 0 ≤ lifetimeCut n := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rcases hb q n hq hn _ _ (degreeCut n) hLU (lifetimeCut n) hy with ⟨hl, hh⟩
  rw [hl] at hlow
  rw [hh] at hhigh
  exact h q hq Λ hΛ n hn η hη hη0 hlow hhigh

/-- P2-AS-01, restrict all-time low and cap-wide high estimates; eq:red-low-target. -/
def S4_AS_01Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q+1 < Λ → ∀ n : ℕ, 2*q ≤ n →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ →
    lowTerminalProbability (V := Fin n) q (degreeCut n) (lifetimeCut n) ≤ epsilon n →
    (∀ L U : ℕ, L ≤ U → U ≤ cap Λ n →
      highWindowProbability (V := Fin n) q L U (degreeCut n) ≤ epsilon n) →
    lowWindowProbability (V := Fin n) q (lowerLocation q Λ η n) (upperLocation q Λ η n)
        (degreeCut n) (lifetimeCut n) ≤ epsilon n ∧
    highLongWindowProbability (V := Fin n) q (lowerLocation q Λ η n) (upperLocation q Λ η n)
        (degreeCut n) (lifetimeCut n) ≤ epsilon n

theorem S4_AS_01_assembly (hb : S4_BRIDGE_01BStatement) (hc : S4_BRIDGE_01CStatement)
    (hm : S4_RED_13AStatement) : S4_AS_01Statement := by
  intro q hq Λ hΛ n hn η hη hη0 hlow hhigh
  rcases hm q hq Λ hΛ n hn η hη hη0 with ⟨hLU,hUM,hL,hU⟩
  constructor
  · exact ((hb q n hq hn).2 _ _ hLU
      (fun G e => lowEdge G (degreeCut n) e ∧ ENNReal.ofReal (lifetimeCut n) < lifetime q G)).2.trans hlow
  · have hmono := (hc q n hq hn _ _ hLU).2.1
      (fun G e => bothHigh G (degreeCut n) e ∧ ENNReal.ofReal (lifetimeCut n) < lifetime q G)
      (fun G e => bothHigh G (degreeCut n) e) (fun _ _ h => h.1)
    exact hmono.trans (hhigh _ _ hLU hUM)

/-- P2-AS-02, uniform onset in eta; thm:proof-window. -/
def S4_AS_02Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q+1 < Λ →
    ∃ N : ℕ, max 3 (2*q) ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ η : ℝ,
      0 < η → η ≤ etaZero Λ → window q Λ η n ≤ (6*Λ/η^2)*n*epsilon n

theorem S4_AS_02_assembly (hlow : CorLowStatement) (hhigh : HighMainStatement)
    (hs : RedSplitStatement) (ha : S4_AS_01Statement) (hp : S4_PAR_01AStatement) :
    S4_AS_02Statement := by
  intro q hq Λ hΛ
  have hΛ0 : 0 < Λ := lt_trans zero_lt_one ((hp q hq).2.2.2 Λ hΛ).1
  obtain ⟨NL,hNL,hlo⟩ := hlow q hq
  obtain ⟨NH,hNH,hhi⟩ := hhigh.2 Λ hΛ0
  refine ⟨max NL NH, hNL.trans (le_max_left _ _), ?_⟩
  intro n hn η hη hη0
  have hnL : NL ≤ n := (le_max_left _ _).trans hn
  have hnH : NH ≤ n := (le_max_right _ _).trans hn
  have hnq : 2*q ≤ n := (le_max_right _ _).trans (hNL.trans hnL)
  have hsplit := ha q hq Λ hΛ n hnq η hη hη0 (hlo n hnL).1
    ((hhi n hnH).2.2 q hq)
  exact (hs q hq Λ hΛ η hη hη0 n hnq hsplit.1 hsplit.2).2

/-- thm:proof-window at the exact frozen interface type. -/
theorem ProofWindow_of_S4 (h : S4_AS_02Statement) (hp : S4_PAR_01BStatement) :
    ProofWindowStatement := by
  intro q hq η hη hη0
  obtain ⟨N,hN,h⟩ := h q hq (capDensity q) (hp q hq)
  exact ⟨N,hN,fun n hn => h n hn η hη hη0⟩

/-- P2-AS-02 in the paper's raw logarithmic scale; eq:proof-window. -/
def S4_AS_02RStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ η : ℝ, 0 < η → η ≤ etaZero (capDensity q) →
    ∃ N : ℕ, max 3 (2*q) ≤ N ∧ ∀ n : ℕ, N ≤ n →
      window q (capDensity q) η n ≤ (6*capDensity q/η^2)*n*
        Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ)/2)

theorem S4_AS_02R_assembly (h : S4_AS_02Statement) (hp : S4_PAR_01BStatement) :
    S4_AS_02RStatement := by
  intro q hq η hη hη0
  obtain ⟨N,hN,hw⟩ := ProofWindow_of_S4 h hp q hq η hη hη0
  refine ⟨N,hN,?_⟩
  intro n hn
  have hn3 : ¬ n < 3 := by have := (le_max_left 3 (2*q)).trans (hN.trans hn); omega
  simpa [epsilon, hn3] using hw n hn

/-- P2-AS-05, mass and arithmetic of the quantile hitting interval; thm:intro-window. -/
def S4_AS_05Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q+1 < Λ → ∀ n : ℕ, 2*q ≤ n →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ →
    upperLocation q Λ η n < cap Λ n →
    1-2*η ≤ terminalProb (V := Fin n) q (lowerLocation q Λ η n)
      (upperLocation q Λ η n+1) (fun _ _ => True) ∧
    ∀ h : ℕ, lowerLocation q Λ η n < h → h ≤ upperLocation q Λ η n+1 →
      0 < (h : ℝ)-lowerLocation q Λ η n ∧
      (h : ℝ)-lowerLocation q Λ η n ≤ window q Λ η n+1

theorem S4_AS_05_assembly (hqnt : PreQuantileStatement) (hp : S4_PAR_01AStatement)
    (hb : S4_BRIDGE_01AStatement) : S4_AS_05Statement := by
  intro q hq Λ hΛ n hn η hη hη0 hUM
  have hn2 : 2 ≤ n := by omega
  have hηhalf : η ≤ 1/2 := hη0.trans ((hp q hq).2.2.2 Λ hΛ).2.2.1.le
  rcases hqnt q n (cap Λ n) hq hn2 η hη hηhalf with
    ⟨hLU,hUM',hCDF,hTail,hTE,hCE,hLo,hHi⟩
  have hLo' := hLo (lowerLocation q Λ η n) le_rfl
  have hHi' := hHi (upperLocation q Λ η n+1) (by change upperLocation q Λ η n < upperLocation q Λ η n+1; omega) (by exact Nat.succ_le_of_lt hUM)
  have hprob := (hb q n hq hn (lowerLocation q Λ η n)
    (upperLocation q Λ η n+1) (by exact le_trans hLU (Nat.le_succ _))).1
  constructor
  · rw [hprob]
    linarith
  · intro h hL hU
    unfold window
    have hL' : (lowerLocation q Λ η n : ℝ) < h := by exact_mod_cast hL
    have hU' : (h : ℝ) ≤ (upperLocation q Λ η n : ℝ)+1 := by exact_mod_cast hU
    constructor <;> linarith

/-- The internal confidence-window conclusion of Theorem 1.2. -/
def ConfidenceWindow (q : ℕ) (α : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, max 3 (2*q) ≤ N ∧
    ∃ m : ℕ → ℤ, Tendsto (fun n : ℕ => (m n : ℝ)/(n : ℝ)) atTop (𝓝 α) ∧
      ∀ n : ℕ, N ≤ n → 1-η ≤ hittingWindowProbability (V := Fin n) q (m n)
        (C*(n : ℝ)*Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ)/2))

/-- P2-AS-06, an error-window bound and quantile limits imply a confidence window. -/
def S4_AS_06Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q+1 < Λ → ∀ α : ℝ,
    QuantileLimits q Λ α → WindowBound q Λ epsilon → ConfidenceWindow q α

theorem S4_AS_06_assembly (hp : S4_PAR_01AStatement) (hs : S4_PAR_06Statement)
    (hc : PreCentreStatement) (hm : S4_AS_05Statement) (hb : S4_BRIDGE_02Statement) :
    S4_AS_06Statement := by
  intro q hq Λ hΛ α hlim hwin η hη hη1
  let θ := min (η/2) (etaZero Λ)
  have hθ : 0 < θ := lt_min (by linarith) ((hp q hq).2.2.2 Λ hΛ).2.1
  have hθ0 : θ ≤ etaZero Λ := min_le_right _ _
  have hθη : 2*θ ≤ η := by have := min_le_left (η/2) (etaZero Λ); dsimp [θ]; linarith
  have hθhalf : θ ≤ 1/2 := hθ0.trans ((hp q hq).2.2.2 Λ hΛ).2.2.1.le
  obtain ⟨K,hK,NW,hNW,hwindow⟩ := hwin θ hθ hθ0
  obtain ⟨NS,hNS,hscale⟩ := hs.2.2
  have hcentre := (hc q hq Λ hΛ θ hθ hθhalf).2.1 (gamma q+1) (by linarith)
  obtain ⟨NC,hcentre⟩ := eventually_atTop.1 hcentre
  let N := max (max NW NS) (max NC (max 3 (2*q)))
  have hNmin : max 3 (2*q) ≤ N :=
    (le_max_right NC _).trans (le_max_right _ _)
  refine ⟨K+1, by linarith, N, hNmin,
    (fun n => (lowerLocation q Λ θ n : ℤ)), ?_, ?_⟩
  · simpa only [Int.cast_natCast] using (hlim θ hθ hθ0).1
  · intro n hn
    have hnW : NW ≤ n := (le_max_left NW NS).trans ((le_max_left _ _).trans hn)
    have hnS : NS ≤ n := (le_max_right NW NS).trans ((le_max_left _ _).trans hn)
    have hnC : NC ≤ n := (le_max_left NC _).trans ((le_max_right _ _).trans hn)
    have hn3 : 3 ≤ n := (le_max_left 3 (2*q)).trans (hNmin.trans hn)
    have hnq : 2*q ≤ n := (le_max_right 3 (2*q)).trans (hNmin.trans hn)
    have henv := hcentre n hnC
    have heps : epsilon n = Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ)/2) := by
      simp [epsilon, show ¬ n < 3 by omega]
    have hscale' := hscale n hnS
    have hw := hwindow n hnW
    have hrad : (upperLocation q Λ θ n : ℝ)+1-lowerLocation q Λ θ n ≤
        (K+1)*(n : ℝ)*Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ)/2) := by
      rw [← heps]
      change (upperLocation q Λ θ n : ℝ)-(lowerLocation q Λ θ n : ℝ) ≤
        K*(n : ℝ)*epsilon n at hw
      nlinarith
    have ha : 0 ≤ (K+1)*(n : ℝ)*Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ)/2) := by
      have hdiff : 0 ≤ (upperLocation q Λ θ n : ℝ)+1-lowerLocation q Λ θ n := by
        have hle : (lowerLocation q Λ θ n : ℝ) ≤ upperLocation q Λ θ n :=
          Nat.cast_le.mpr henv.1
        linarith
      exact hdiff.trans hrad
    have hi := (hb q n hq hnq (lowerLocation q Λ θ n : ℤ) _ ha).2.2
      (lowerLocation q Λ θ n) (upperLocation q Λ θ n) henv.1 rfl hrad
    have hmass := (hm q hq Λ hΛ n hnq θ hθ hθ0 henv.2.2).1
    exact (show 1-η ≤ 1-2*θ by linarith).trans (hmass.trans hi)

end ThLean.BP.S4

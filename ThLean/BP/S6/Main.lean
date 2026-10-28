import ThLean.BP.S6.Descent

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S6

/-- Restricted finite terminal event; no graph or edge is evaluated at infinity. -/
def windowProbability {n : ℕ} (q L U D : ℕ) (z : Graph n → ℝ) (x : ℝ) : ℝ :=
  terminalWindowProbability q L U (fun G e => bothHigh G D e ∧ x < z G)

/-- Every unordered pair has an endpoint, so both-high implies high. -/
theorem bothHigh_implies_highEdge {n : ℕ} (G : Graph n) (D : ℕ) (e : Edge n)
    (h : bothHigh G D e) : highEdge G D e := by
  have he : ∃ a, Touches a e.val :=
    Sym2.inductionOn e.val (fun a b => ⟨a, b, rfl⟩)
  obtain ⟨a, ha⟩ := he
  exact ⟨a, ha, h a ha⟩

/-- P4-HIGH-40; sum of pivotal densities to root occupation, lines 414--424. Paper label: `thm:high-main`; blueprint ID: `P4-HIGH-40`. -/
def S6_40Statement : Prop := ∀ (n q : ℕ) (Λ : ℝ), 3 ≤ n → 3 ≤ q → 0 < Λ →
  ∀ (w : ℕ) (u : Fin n), pivotalCut Λ ≤ w →
    (∑ j ∈ Finset.Ico (w + 1) (cap Λ n),
      ∑ m ∈ Finset.Ico j (cap Λ n), pivMean n q m (pivotalCut Λ) j) ≤
    (2 * Λ / (w - pivotalCut Λ + 2 : ℕ)) * ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 *
      ∑ t ∈ Finset.range (cap Λ n), rootGeMean n q t w u

/-- P4-HIGH-41; explicit bound of thm. high-main, retaining frozen highBound. Paper label: `thm:high-main`; blueprint ID: `P4-HIGH-41`. -/
def S6_41Statement : Prop := ∀ (n q : ℕ) (Λ : ℝ), 3 ≤ n → 3 ≤ q → 0 < Λ →
  pivotalCut Λ ≤ descentCut n →
    highTerminalProbability (V := Fin n) q (cap Λ n) (degreeCut n) ≤ highBound Λ n

theorem S6_41_assembly (h31 : S6_31Statement) (h33 : S6_33Statement)
    (h39 : S6_39Statement) (h40 : S6_40Statement) : S6_41Statement := by
  intro n q Λ hn hq hΛ hw
  have hp := h33 n Λ hn hΛ
  let u : Fin n := ⟨0, by omega⟩
  have ho := h31 n q Λ hn hq hΛ u (descentCut n) (hp.wpos hw)
  have hpiv := h40 n q Λ hn hq hΛ (descentCut n) u hw
  have hd := h39 n q Λ hn hq hΛ
  let C : ℝ := (2 * Λ / (descentCut n - pivotalCut Λ + 2 : ℕ)) *
    ((n : ℝ) / ((n : ℝ) - 1)) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound := hpiv.trans (mul_le_mul_of_nonneg_left ho hC)
  have hsum := hd.trans (add_le_add_right (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 8 / 3)) _)
  convert hsum using 1
  unfold highBound
  simp only [alpha, one_div, zpow_neg, zpow_natCast, inv_pow]
  ring

/-- P4-HIGH-44b; finite terminal-event inclusion, including L=U and M=0. Paper label: `thm:high-main`; blueprint ID: `P4-HIGH-44b`. -/
def S6_44bStatement : Prop := ∀ (n q M D L U : ℕ), 3 ≤ n → 3 ≤ q →
  L ≤ U → U ≤ M → ∀ A : Graph n → Edge n → Prop,
    (∀ G e, A G e → highEdge G D e) →
    terminalWindowProbability q L U A ≤ highTerminalProbability (V := Fin n) q M D

/-- P4-HIGH-44; explicit cutoff and every window conclusion of thm. high-main. Paper label: `thm:high-main`; blueprint ID: `P4-HIGH-44`. -/
def S6_44Statement : Prop := ∀ (Λ : ℝ), 0 < Λ →
  ∀ n q : ℕ, sizeCutoff Λ ≤ n → 3 ≤ q →
    pivotalCut Λ ≤ descentCut n ∧
    highTerminalProbability (V := Fin n) q (cap Λ n) (degreeCut n) ≤ highBound Λ n ∧
    highBound Λ n ≤ epsilon n ∧
    (∀ L U : ℕ, L ≤ U → U ≤ cap Λ n →
      windowProbability (n := n) q L U (degreeCut n) (fun _ => 0) (-1) ≤ epsilon n)

theorem S6_44_assembly (h41 : S6_41Statement) (h43 : S6_43Statement)
    (ha : S6_44aStatement) (hb : S6_44bStatement) : S6_44Statement := by
  intro Λ hΛ n q hn hq
  obtain ⟨hn3, ht⟩ := ha n Λ hΛ hn
  obtain ⟨hw, _, herr⟩ := h43 n Λ hn3 hΛ ht
  have hmain := h41 n q Λ hn3 hq hΛ hw
  refine ⟨hw, hmain, herr, ?_⟩
  intro L U hLU hU
  exact (hb n q (cap Λ n) (degreeCut n) L U hn3 hq hLU hU
    (fun G e => bothHigh G (degreeCut n) e ∧ (-1 : ℝ) < 0)
    (fun G e h => bothHigh_implies_highEdge G (degreeCut n) e h.1)).trans (hmain.trans herr)

/-- P4-HIGH-45; high-degree input to prop. red-split, for every terminal weight. Paper label: `eq:red-high`; blueprint ID: `P4-HIGH-45`. -/
def S6_45Statement : Prop := ∀ (Λ : ℝ), 0 < Λ → ∀ n q : ℕ,
  max (2 * q) (sizeCutoff Λ) ≤ n → 3 ≤ q → ∀ L U : ℕ,
  L ≤ U → U ≤ cap Λ n → ∀ (z : Graph n → ℝ) (x : ℝ),
    windowProbability q L U (degreeCut n) z x ≤ epsilon n

theorem S6_45_assembly (h44 : S6_44Statement) (ha : S6_44aStatement)
    (hb : S6_44bStatement) : S6_45Statement := by
  intro Λ hΛ n q hn hq L U hLU hU z x
  have hnsize := (le_max_right (2 * q) (sizeCutoff Λ)).trans hn
  have hn3 := (ha n Λ hΛ hnsize).1
  have hmain := h44 Λ hΛ n q hnsize hq
  exact (hb n q (cap Λ n) (degreeCut n) L U hn3 hq hLU hU
    (fun G e => bothHigh G (degreeCut n) e ∧ x < z G)
    (fun G e h => bothHigh_implies_highEdge G (degreeCut n) e h.1)).trans
    (hmain.2.1.trans hmain.2.2.1)

end ThLean.BP.S6

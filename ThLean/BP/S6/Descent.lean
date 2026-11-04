module

public import ThLean.BP.S6.Deletion
public import ThLean.BP.S6.Analytic

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S6

/-- P4-HIGH-32a; terminal bridge and total hazard budget, high-descent-1. Paper label: `eq:high-descent-1`; blueprint ID: `P4-HIGH-32a`. -/
def S6_32aStatement : Prop := ∀ (n q M D : ℕ), 3 ≤ n → 3 ≤ q →
  highTerminalProbability (V := Fin n) q M D =
    ∑ m ∈ Finset.range M, meanGraph (n := n) m (kappaKind q (fun G e => highEdge G D e)) ∧
  (∑ m ∈ Finset.range M, meanGraph (n := n) m (kappa q)) ≤ 1 ∧
  (∑ m ∈ Finset.range M, meanGraph (n := n) m (kappa q)) =
    uniformProb (fun x : Hist n M => cappedLast q x < M)

/-- P4-HIGH-32b; oriented high-endpoint count, high-descent-1. Paper label: `eq:high-descent-1`; blueprint ID: `P4-HIGH-32b`. -/
def S6_32bStatement : Prop := ∀ (n q m D : ℕ), 3 ≤ n → 3 ≤ q →
  meanGraph (n := n) m (kappaKind q (fun G e => highEdge G D e)) ≤
    2 * ∑ j ∈ Finset.Ico (D + 1) (m + 1), degreeMean n q m j

/-- P4-HIGH-32; terminal estimate and total hazard, eq. high-descent-1. Paper label: `eq:high-descent-1`; blueprint ID: `P4-HIGH-32`. -/
def S6_32Statement : Prop := ∀ (n q M D : ℕ), 3 ≤ n → 3 ≤ q →
  highTerminalProbability (V := Fin n) q M D ≤
    2 * ∑ m ∈ Finset.range M, ∑ j ∈ Finset.Ico (D + 1) (m + 1), degreeMean n q m j ∧
  (∑ m ∈ Finset.range M, meanGraph (n := n) m (kappa q)) ≤ 1 ∧
  (∑ m ∈ Finset.range M, meanGraph (n := n) m (kappa q)) =
    uniformProb (fun x : Hist n M => cappedLast q x < M)

theorem S6_32_assembly (ha : S6_32aStatement) (hb : S6_32bStatement) :
    S6_32Statement := by
  intro n q M D hn hq
  obtain ⟨heq, htotal, hevent⟩ := ha n q M D hn hq
  refine ⟨?_, htotal, hevent⟩
  rw [heq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun m _ => hb n q m D hn hq)

/-- P4-HIGH-34; one-step density recurrence, eq. high-recursion. Paper label: `eq:high-recursion`; blueprint ID: `P4-HIGH-34`. -/
def S6_34Statement : Prop := ∀ (n q : ℕ) (Λ : ℝ), 3 ≤ n → 3 ≤ q → 0 < Λ →
  ∀ m j : ℕ, 1 ≤ j → j ≤ m → m ≤ cap Λ n →
    degreeMean n q m j ≤ pivMean n q m (pivotalCut Λ) j + alpha * degreeMean n q (m - 1) (j - 1)

theorem S6_34_assembly (h01 : S6_01aStatement) (h04 : S6_04aStatement)
    (h11 : S6_11Statement) (h33 : S6_33Statement) : S6_34Statement := by
  intro n q Λ hn hq hΛ m j hj hjm hm
  have hp := h33 n Λ hn hΛ
  have hsplit : degreeMean n q m j = npMean n q m (pivotalCut Λ) j +
      pivMean n q m (pivotalCut Λ) j := by
    unfold degreeMean npMean pivMean meanGraph
    simp_rw [(h04 n q hn hq _ j (pivotalCut Λ) hp.Kpos).2.2.2.1]
    exact (h01 (Hist n m)).add _ _
  have hnon : 0 ≤ degreeMean n q (m - 1) (j - 1) :=
    (h01 (Hist n (m - 1))).nonneg _ (fun x =>
      (h04 n q hn hq (tupleGraph x) (j - 1) (pivotalCut Λ) hp.Kpos).1)
  have hnp := h11 n q m j (pivotalCut Λ) hn hq (by omega) hj hp.Kpos
  have hcoef := hp.contraction m hm
  change _ ≤ alpha at hcoef
  rw [hsplit]
  linarith [mul_le_mul_of_nonneg_right hcoef hnon]

/-- P4-HIGH-35; triangular recurrence iteration, eq. high-iterate. Paper label: `eq:high-iterate`; blueprint ID: `P4-HIGH-35`. -/
def S6_35Statement : Prop := ∀ (M : ℕ) (a b : ℕ → ℕ → ℝ),
  (∀ m j, 0 ≤ a m j) → (∀ m j, 0 ≤ b m j) →
  (∀ m j, 1 ≤ j → j ≤ m → m < M → a m j ≤ b m j + alpha * a (m - 1) (j - 1)) →
  ∀ w j m : ℕ, w < j → j ≤ m → m < M →
    a m j ≤ (∑ k ∈ Finset.Ico (w + 1) (j + 1), alpha ^ (j - k) * b (m - j + k) k) +
      alpha ^ (j - w) * a (m - j + w) w

/-- P4-HIGH-37; sum the shifted base terms, high-descent lines 163--170. Paper label: `prop:high-descent`; blueprint ID: `P4-HIGH-37`. -/
def S6_37Statement : Prop := ∀ (M D w : ℕ) (a : ℕ → ℕ → ℝ) (h : ℕ → ℝ),
  w < D → (∀ m j, 0 ≤ a m j) → (∀ t, 0 ≤ h t) →
  (∀ t, t < M → a t w ≤ h t) → (∑ t ∈ Finset.range M, h t) ≤ 1 →
  2 * (∑ j ∈ Finset.Ico (D + 1) M, ∑ m ∈ Finset.Ico j M,
    alpha ^ (j - w) * a (m - j + w) w) ≤ (8 / 3 : ℝ) * alpha ^ (D + 1 - w)

/-- P4-HIGH-38; shifted pivotal convolution, high-descent lines 173--177. Paper label: `prop:high-descent`; blueprint ID: `P4-HIGH-38`. -/
def S6_38Statement : Prop := ∀ (M D w : ℕ) (b : ℕ → ℕ → ℝ),
  w < D → (∀ m j, 0 ≤ b m j) →
  2 * (∑ j ∈ Finset.Ico (D + 1) M, ∑ m ∈ Finset.Ico j M,
    ∑ k ∈ Finset.Ico (w + 1) (j + 1), alpha ^ (j - k) * b (m - j + k) k) ≤
  (8 / 3 : ℝ) * ∑ k ∈ Finset.Ico (w + 1) M, ∑ t ∈ Finset.Ico k M, b t k

/-- P4-HIGH-39a; triangular finite-sum reindexing used in prop. high-descent. Paper label: `prop:high-descent`; blueprint ID: `P4-HIGH-39a`. -/
def S6_39aStatement : Prop := ∀ (M D : ℕ) (a : ℕ → ℕ → ℝ),
  (∑ m ∈ Finset.range M, ∑ j ∈ Finset.Ico (D + 1) (m + 1), a m j) =
    ∑ j ∈ Finset.Ico (D + 1) M, ∑ m ∈ Finset.Ico j M, a m j

/-- P4-HIGH-39; prop. high-descent, valid also when the process cap is zero. Paper label: `prop:high-descent`; blueprint ID: `P4-HIGH-39`. -/
def S6_39Statement : Prop := ∀ (n q : ℕ) (Λ : ℝ), 3 ≤ n → 3 ≤ q → 0 < Λ →
  highTerminalProbability (V := Fin n) q (cap Λ n) (degreeCut n) ≤
    (8 / 3 : ℝ) * alpha ^ (degreeCut n + 1 - descentCut n) +
      (8 / 3 : ℝ) * ∑ j ∈ Finset.Ico (descentCut n + 1) (cap Λ n),
        ∑ m ∈ Finset.Ico j (cap Λ n), pivMean n q m (pivotalCut Λ) j

theorem S6_39_assembly (h01 : S6_01aStatement) (h04 : S6_04aStatement)
    (h32 : S6_32Statement) (h33 : S6_33Statement) (h34 : S6_34Statement)
    (h35 : S6_35Statement) (h37 : S6_37Statement) (h38 : S6_38Statement)
    (hr : S6_39aStatement) : S6_39Statement := by
  intro n q Λ hn hq hΛ
  let M := cap Λ n
  let D := degreeCut n
  let w := descentCut n
  let K := pivotalCut Λ
  let a := degreeMean n q
  let b := fun m j => pivMean n q m K j
  have hp := h33 n Λ hn hΛ
  have ha : ∀ m j, 0 ≤ a m j := fun m j =>
    (h01 (Hist n m)).nonneg _ (fun x => (h04 n q hn hq (tupleGraph x) j K hp.Kpos).1)
  have hb : ∀ m j, 0 ≤ b m j := fun m j =>
    (h01 (Hist n m)).nonneg _ (fun x => (h04 n q hn hq (tupleGraph x) j K hp.Kpos).2.2.1)
  have hrec : ∀ m j, 1 ≤ j → j ≤ m → m < M →
      a m j ≤ b m j + alpha * a (m - 1) (j - 1) :=
    fun m j hj hjm hm => h34 n q Λ hn hq hΛ m j hj hjm (Nat.le_of_lt hm)
  have hi := h35 M a b ha hb hrec
  have hs : (∑ j ∈ Finset.Ico (D + 1) M, ∑ m ∈ Finset.Ico j M, a m j) ≤
      (∑ j ∈ Finset.Ico (D + 1) M, ∑ m ∈ Finset.Ico j M,
        ∑ k ∈ Finset.Ico (w + 1) (j + 1), alpha ^ (j - k) * b (m - j + k) k) +
      (∑ j ∈ Finset.Ico (D + 1) M, ∑ m ∈ Finset.Ico j M,
        alpha ^ (j - w) * a (m - j + w) w) := by
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro m hm
    exact hi w j m (by have := hp.wlt; simp only [Finset.mem_Ico] at hj; omega)
      (Finset.mem_Ico.mp hm).1 (Finset.mem_Ico.mp hm).2
  let h := fun t => meanGraph (n := n) t (kappa q)
  have hh : ∀ t, 0 ≤ h t := fun t =>
    (h01 (Hist n t)).nonneg _ (fun G => le_trans (h04 n q hn hq (tupleGraph G) w K hp.Kpos).1
      (h04 n q hn hq (tupleGraph G) w K hp.Kpos).2.2.2.2.1)
  have hah : ∀ t, t < M → a t w ≤ h t := fun t _ =>
    (h01 (Hist n t)).mono _ _ (fun x => (h04 n q hn hq (tupleGraph x) w K hp.Kpos).2.2.2.2.1)
  have hbase := h37 M D w a h hp.wlt ha hh hah (h32 n q M D hn hq).2.1
  have hpiv := h38 M D w b hp.wlt hb
  have hterm := (h32 n q M D hn hq).1
  rw [hr] at hterm
  change highTerminalProbability (V := Fin n) q M D ≤ _
  linarith

end ThLean.BP.S6

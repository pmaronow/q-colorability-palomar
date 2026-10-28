import ThLean.BP.S4.Bridges
import ThLean.Contrib.S434.Bridge01C

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S434
open ThresholdFoundations ThLean.BP.S4 ThLean.Contrib.S434

private theorem pair_nonempty {n : ℕ} (hn : 2 ≤ n) : Nonempty (Pair (Fin n)) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    simp [a, b] at hv
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hv
  have he := Sym2.eq_iff.mp hv
  rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  all_goals exact hab (ha.trans hb.symm)

private theorem tupleGraph_loopless {n m : ℕ} (x : EdgeTuple (Fin n) m) :
    Loopless (tupleGraph x) := by
  intro v
  unfold tupleGraph
  apply Finset.card_eq_zero.mpr
  ext i
  constructor
  · intro hi
    simp only [Finset.mem_filter] at hi
    exact False.elim ((x i).property v hi.2)
  · intro hi
    simp at hi

private theorem terminalReal_mono {n q L U : ℕ} (hn : 2 ≤ n)
    (F J : ℕ → MGraph (Fin n) → Pair (Fin n) → ℝ)
    (h : ∀ k G e, L < k → k ≤ U → Loopless G → Colorable q G →
      ¬ Colorable q (addPair G e) → F k G e ≤ J k G e) :
    terminalReal (V := Fin n) q L U F ≤ terminalReal q L U J := by
  classical
  letI : Nonempty (Pair (Fin n)) := pair_nonempty hn
  unfold terminalReal uniformMean
  apply Finset.sum_le_sum
  intro m hm
  letI : Nonempty (EdgeTuple (Fin n) m) :=
    ⟨fun _ => Classical.choice (pair_nonempty hn)⟩
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  apply Finset.sum_le_sum
  intro x hx
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  apply Finset.sum_le_sum
  intro e he
  by_cases hf : Colorable q (tupleGraph x) ∧
      ¬ Colorable q (addPair (tupleGraph x) e)
  · have hmL := (Finset.mem_Ico.mp hm).1
    have hmU := (Finset.mem_Ico.mp hm).2
    have hL : L < m+1 := by omega
    have hU : m+1 ≤ U := by omega
    simp only [if_pos hf]
    exact h (m+1) (tupleGraph x) e hL hU (tupleGraph_loopless x) hf.1 hf.2
  · simp [hf]

private theorem indicator_mono {P Q : Prop} (h : P → Q) : indicator P ≤ indicator Q := by
  classical
  unfold indicator
  split_ifs with hp hq
  · exact le_rfl
  · exact False.elim (hq (h hp))
  · norm_num
  · exact le_rfl

/-- The only unresolved part is the standalone terminal-mass normalization node. -/
theorem S4_BRIDGE_01CStatement_from_normalization
    (hNorm : S4_BRIDGE_01CNormalizationStatement) : S4_BRIDGE_01CStatement := by
  intro q n hq hn L U hLU
  have hn2 : 2 ≤ n := by omega
  refine ⟨hNorm q n hq hn L U hLU, ?_, ?_⟩
  · intro P Q hPQ
    unfold terminalProb
    apply terminalReal_mono hn2
    intro k G e hk hku hLoop hc hfail
    exact indicator_mono (hPQ G e)
  · intro F J hFJ
    exact terminalReal_mono hn2 F J hFJ

end ThLean.W.S434

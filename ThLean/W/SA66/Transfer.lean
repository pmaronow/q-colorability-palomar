import ThLean.BP.SA.Transfer
import ThLean.W.BR01.PairBridge

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA66

open ThresholdFoundations
open ThLean.BP.SA

private def injectiveFunctionsEquivEmbedding {α β : Type*} :
    {f : α → β // Function.Injective f} ≃ (α ↪ β) where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f, f.injective⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

private theorem distinctProbability_cardinality (n m : ℕ) :
    distinctProbability n m =
      (Fintype.card {x : EdgeTuple (Fin n) m // DistinctPrefix x} : ℝ) /
        (Fintype.card (EdgeTuple (Fin n) m) : ℝ) := by
  classical
  simp [distinctProbability, uniformProb, uniformMean, indicator,
    Fintype.card_subtype]

private theorem birthdayProduct_eq_descFactorial (B m : ℕ)
    (hB : 0 < B) (hm : m ≤ B) :
    (∏ i ∈ Finset.range m, (1 - (i : ℝ) / (B : ℝ))) =
      (B.descFactorial m : ℝ) / (B : ℝ) ^ m := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  calc
    (∏ i ∈ Finset.range m, (1 - (i : ℝ) / (B : ℝ))) =
        ∏ i ∈ Finset.range m, ((B - i : ℕ) : ℝ) / (B : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hiB : i < B := lt_of_lt_of_le (Finset.mem_range.mp hi) hm
      have hcast : ((B - i : ℕ) : ℝ) = (B : ℝ) - (i : ℝ) := by
        exact Nat.cast_sub (Nat.le_of_lt hiB)
      rw [hcast]
      field_simp [hB0]
    _ = (∏ i ∈ Finset.range m, ((B - i : ℕ) : ℝ)) /
          (B : ℝ) ^ m := by
      rw [Finset.prod_div_distrib]
      simp
    _ = (B.descFactorial m : ℝ) / (B : ℝ) ^ m := by
      have hprod :
          (∏ i ∈ Finset.range m, ((B - i : ℕ) : ℝ)) =
            (B.descFactorial m : ℝ) := by
        exact_mod_cast (Nat.descFactorial_eq_prod_range B m).symm
      rw [hprod]

theorem SA_X50bStatement_holds : ThLean.BP.SA.SA_X50bStatement := by
  intro n m hn hm
  let B : ℕ := n.choose 2
  have hpair := ThLean.W.BR01.PairBridgeStatement_holds n
  have hpairCard : Fintype.card (Pair (Fin n)) = B := by
    simpa [B] using hpair.2.1
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.choose_pos (by omega : 2 ≤ n)
  have hInjCard :
      Fintype.card {x : EdgeTuple (Fin n) m // DistinctPrefix x} =
        B.descFactorial m := by
    calc
      Fintype.card {x : EdgeTuple (Fin n) m // DistinctPrefix x} =
          Fintype.card (Fin m ↪ Pair (Fin n)) :=
        Fintype.card_congr injectiveFunctionsEquivEmbedding
      _ = (Fintype.card (Pair (Fin n))).descFactorial (Fintype.card (Fin m)) :=
        Fintype.card_embedding_eq
      _ = B.descFactorial m := by simp [hpairCard]
  have hAllCard : Fintype.card (EdgeTuple (Fin n) m) = B ^ m := by
    simp [EdgeTuple, hpairCard]
  have hprob : distinctProbability n m =
      (B.descFactorial m : ℝ) / (B : ℝ) ^ m := by
    rw [distinctProbability_cardinality, hInjCard, hAllCard]
    norm_cast
  have hproduct := birthdayProduct_eq_descFactorial B m hB hm
  constructor
  · rw [hprob]
    exact hproduct.symm
  · rw [hprob, ← hproduct]
    apply Finset.prod_pos
    intro i hi
    have hiB : i < B := lt_of_lt_of_le (Finset.mem_range.mp hi) hm
    have hcast : (i : ℝ) < (B : ℝ) := by exact_mod_cast hiB
    rw [sub_pos]
    exact (div_lt_one (by exact_mod_cast hB)).2 hcast

example : ThLean.BP.SA.SA_X50bStatement := SA_X50bStatement_holds

end ThLean.W.SA66

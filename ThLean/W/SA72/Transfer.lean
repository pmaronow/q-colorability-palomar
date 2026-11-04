module

public import ThLean.BP.SA.Transfer
public import ThLean.W.BR01.PairBridge

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA72
open ThresholdFoundations

private theorem completeEdges_card (n : ℕ) :
    (completeEdges (V := Fin n)).card = n.choose 2 := by
  let S := completeEdges (V := Fin n)
  have hp : Fintype.card (Pair (Fin n)) = n.choose 2 :=
    (ThLean.W.BR01.PairBridgeStatement_holds n).2.1
  let e : {z : Sym2 (Fin n) // z ∈ S} ≃ ThresholdFoundations.Pair (Fin n) :=
    { toFun := fun z : {z : Sym2 (Fin n) // z ∈ S} =>
        (⟨z.val, by simpa [S, completeEdges] using z.property⟩ : ThresholdFoundations.Pair (Fin n))
      invFun := fun z : ThresholdFoundations.Pair (Fin n) =>
        (⟨z.val, by simpa [S, completeEdges] using z.property⟩ : {z : Sym2 (Fin n) // z ∈ S})
      left_inv := by intro z; cases z; rfl
      right_inv := by intro z; cases z; rfl }
  calc
    S.card = Fintype.card {z : Sym2 (Fin n) // z ∈ S} := by
      symm
      exact Fintype.card_coe S
    _ = Fintype.card (Pair (Fin n)) := Fintype.card_congr e
    _ = n.choose 2 := hp

private theorem simpleGraphsWithEdges_eq_powersetCard (n j : ℕ) :
    simpleGraphsWithEdges (V := Fin n) j =
      (completeEdges (V := Fin n)).powersetCard j := by
  unfold simpleGraphsWithEdges
  rw [← Finset.powersetCard_eq_filter]

private theorem bernoulli_mixture (q n : ℕ) (p : ℝ) :
    bernoulliProbability (V := Fin n) q p =
      ∑ j ∈ Finset.range (n.choose 2 + 1),
        binomialWeight (n.choose 2) p j * simpleProbability (V := Fin n) q j := by
  classical
  let S := completeEdges (V := Fin n)
  let B := n.choose 2
  have hS : S.card = B := completeEdges_card n
  have hgroup :
      bernoulliProbability (V := Fin n) q p =
        ∑ j ∈ Finset.range (B + 1),
          ∑ E ∈ S.powersetCard j,
            (p ^ j * (1 - p) ^ (B - j)) *
              indicator (Colorable q (simpleGraph E)) := by
    rw [bernoulliProbability]
    simp_rw [Fintype.card_fin]
    rw [Finset.sum_powerset, hS]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro E hE
    have hcard : E.card = j := (Finset.mem_powersetCard.mp hE).2
    rw [hcard]
  have hcounts :
      (∑ j ∈ Finset.range (B + 1),
          ∑ E ∈ S.powersetCard j,
            (p ^ j * (1 - p) ^ (B - j)) *
              indicator (Colorable q (simpleGraph E))) =
        ∑ j ∈ Finset.range (B + 1),
          (p ^ j * (1 - p) ^ (B - j)) *
            (((S.powersetCard j).filter
              (fun E => Colorable q (simpleGraph E))).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum]
    simp [indicator]
  have hterm : ∀ j ∈ Finset.range (B + 1),
      (p ^ j * (1 - p) ^ (B - j)) *
          (((S.powersetCard j).filter
            (fun E => Colorable q (simpleGraph E))).card : ℝ) =
        binomialWeight B p j * simpleProbability (V := Fin n) q j := by
    intro j hj
    have hjB : j ≤ B := by
      exact Nat.le_of_lt_succ (by
        simpa only [Nat.add_one] using Finset.mem_range.mp hj)
    have hclass : simpleGraphsWithEdges (V := Fin n) j = S.powersetCard j := by
      rw [simpleGraphsWithEdges_eq_powersetCard]
    have hdenPow : (S.powersetCard j).card = B.choose j := by
      rw [Finset.card_powersetCard, hS]
    rw [simpleProbability, hclass, hdenPow]
    rw [binomialWeight, if_pos hjB]
    have hchoose : (B.choose j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hjB))
    field_simp
  rw [hgroup, hcounts]
  apply Finset.sum_congr rfl
  intro j hj
  exact hterm j hj

private theorem binomialWeight_nonneg (B : ℕ) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (j : ℕ) : 0 ≤ binomialWeight B p j := by
  unfold binomialWeight
  split
  · next hj => positivity
  · positivity

private theorem binomialWeight_sum (B : ℕ) (p : ℝ) :
    (∑ j ∈ Finset.range (B + 1), binomialWeight B p j) = 1 := by
  calc
    (∑ j ∈ Finset.range (B + 1), binomialWeight B p j) =
        ∑ j ∈ Finset.range (B + 1),
          p ^ j * (1 - p) ^ (B - j) * (B.choose j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjB : j ≤ B := Nat.le_of_lt_succ (by
        simpa only [Nat.add_one] using Finset.mem_range.mp hj)
      simp [binomialWeight, hjB]
      ring
    _ = (p + (1 - p)) ^ B := by rw [add_pow]
    _ = 1 := by ring

theorem SA_X54Statement_holds : ThLean.BP.SA.SA_X54Statement := by
  intro q n hq hn p hp0 hp1
  refine ⟨bernoulli_mixture q n p, ?_, ?_⟩
  · intro j
    exact binomialWeight_nonneg (n.choose 2) p hp0 hp1 j
  · exact binomialWeight_sum (n.choose 2) p

example : ThLean.BP.SA.SA_X54Statement := SA_X54Statement_holds

end ThLean.W.SA72

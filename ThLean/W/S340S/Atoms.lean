module

public import ThLean.W.S340S.Words
public import ThLean.W.S340S.Masses

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations hiding neighborList
open ThLean.BP.S3
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S340S
universe u
set_option maxHeartbeats 800000

theorem poissonWordProb_eq_weighted {V : Type u} [Fintype V]
    (t : ℝ) (P : List (Pair V) → Prop) :
    poissonWordProb t P = weightedListMean t
      (fun _ : Pair V => 1 / (Fintype.card (Pair V) : ℝ)) (fun w => indicator (P w)) := by
  simp [weightedListMean,poissonWordProb,poissonMixture,uniformProb,uniformMean,
    EdgeTuple,Finset.prod_const]
  apply tsum_congr
  intro k
  congr 1
  rw [← Finset.mul_sum,div_eq_mul_inv]
  ring

theorem blockWords_mass {V : Type u} [Fintype V] (S : Finset V)
    (hV : 2 ≤ Fintype.card V) (hS : 0 < (Finset.univ \ S).card)
    (B : MGraph (Outside S)) (C : MGraph (Inside S))
    (ys : Inside S → List V) (hy : ∀ a v, v ∈ ys a → v ∈ Finset.univ \ S) (t : ℝ) :
    (∏ j : SplitIndex S, poissonListMass (t * blockMass S j)
      (fun _ : Pair V => (1 / (Fintype.card (Pair V) : ℝ)) / blockMass S j)
      (blockWords S B C ys hy j)) =
    (∏ p : Pair (Outside S), poissonWeight (t / Fintype.card (Pair V)) (B p.val)) *
    (∏ p : Pair (Inside S), poissonWeight (t / Fintype.card (Pair V)) (C p.val)) *
    ∏ a : Inside S, poissonListMass (t * (Finset.univ \ S).card / Fintype.card (Pair V))
      (fun v : V => if v ∈ Finset.univ \ S then 1 / ((Finset.univ \ S).card : ℝ) else 0)
      (ys a) := by
  have hN : (Fintype.card (Pair V) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (ThLean.W.S302.S3_03aStatement_holds V hV).2.1
  have hM : (((Finset.univ \ S).card : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  have hout (p : Pair (Outside S)) :
      poissonListMass (t * blockMass S (.inl p))
        (fun _ : Pair V => (1 / (Fintype.card (Pair V) : ℝ)) / blockMass S (.inl p))
        (blockWords S B C ys hy (.inl p)) =
      poissonWeight (t / Fintype.card (Pair V)) (B p.val) := by
    simp [blockWords,poissonListMass,hN,div_eq_mul_inv]
  have hin (p : Pair (Inside S)) :
      poissonListMass (t * blockMass S (.inr (.inl p)))
        (fun _ : Pair V => (1 / (Fintype.card (Pair V) : ℝ)) / blockMass S (.inr (.inl p)))
        (blockWords S B C ys hy (.inr (.inl p))) =
      poissonWeight (t / Fintype.card (Pair V)) (C p.val) := by
    simp [blockWords,poissonListMass,hN,div_eq_mul_inv]
  have hcross (a : Inside S) :
      poissonListMass (t * blockMass S (.inr (.inr a)))
        (fun _ : Pair V => (1 / (Fintype.card (Pair V) : ℝ)) / blockMass S (.inr (.inr a)))
        (blockWords S B C ys hy (.inr (.inr a))) =
      poissonListMass (t * (Finset.univ \ S).card / Fintype.card (Pair V))
        (fun v : V => if v ∈ Finset.univ \ S then 1 / ((Finset.univ \ S).card : ℝ) else 0)
        (ys a) := by
    have hnorm : (1 / (Fintype.card (Pair V) : ℝ)) /
        (((Finset.univ \ S).card : ℝ) / Fintype.card (Pair V)) =
        1 / ((Finset.univ \ S).card : ℝ) := by field_simp
    have hmap : (ys a).map (fun v : V => if v ∈ Finset.univ \ S then
        1 / ((Finset.univ \ S).card : ℝ) else 0) =
        (ys a).map (fun _ => 1 / ((Finset.univ \ S).card : ℝ)) := by
      apply List.map_congr_left
      intro v hv
      simp [hy a v hv]
    simp only [blockMass_cross,hnorm,blockWords,poissonListMass,neighborWord_length,hmap]
    simp [mul_div_assoc,neighborWord]
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  simp_rw [hout,hin,hcross]
  ring

theorem split_loopless {V : Type u} [Fintype V]
    (h35 : S3_35aStatement.{u}) (S : Finset V)
    (hV : 2 ≤ Fintype.card V) (hS : 0 < (Finset.univ \ S).card)
    (t : ℝ) (ht : 0 ≤ t) (B : MGraph (Outside S)) (C : MGraph (Inside S))
    (hB : Loopless B) (hC : Loopless C)
    (ys : Inside S → List V) (hy : ∀ a v, v ∈ ys a → v ∈ Finset.univ \ S) :
    poissonWordProb t (fun w => inducedGraph (listGraph w) (Finset.univ \ S) = B ∧
      inducedGraph (listGraph w) S = C ∧ ∀ a, neighborList a.val (Finset.univ \ S) w = ys a) =
    poissonGraphMean (t * ((Finset.univ \ S).card.choose 2) / Fintype.card (Pair V))
      (fun G => indicator (G = B)) *
    poissonGraphMean (t * (S.card.choose 2) / Fintype.card (Pair V))
      (fun G => indicator (G = C)) *
    ∏ a : Inside S, poissonListMass (t * (Finset.univ \ S).card / Fintype.card (Pair V))
      (fun v : V => if v ∈ Finset.univ \ S then 1 / ((Finset.univ \ S).card : ℝ) else 0)
      (ys a) := by
  letI : Nonempty (Pair V) := ThLean.W.S339.pair_nonempty_of_card_ge_two hV
  have hN : 0 < (Fintype.card (Pair V) : ℝ) := by
    exact_mod_cast (ThLean.W.S302.S3_03aStatement_holds V hV).2.1
  have hs := finite_splitting h35
    (fun _ : Pair V => 1 / (Fintype.card (Pair V) : ℝ)) (blockLabel S) t
    (uniformPair_probability hV) ht
    (fun j => by simpa only [blockMass] using blockMass_pos S hV hS j)
    (blockWords S B C ys hy) (blockWords_label S B C ys hy)
  rw [poissonWordProb_eq_weighted]
  calc
    _ = weightedListMean t (fun _ : Pair V => 1 / (Fintype.card (Pair V) : ℝ))
        (fun w => indicator (∀ j, blockSublist S j w = blockWords S B C ys hy j)) := by
      congr 1
      funext w
      exact congrArg indicator (propext (blockWords_event S B C hB hC ys hy w).symm)
    _ = ∏ j : SplitIndex S, poissonListMass (t * blockMass S j)
        (fun _ : Pair V => (1 / (Fintype.card (Pair V) : ℝ)) / blockMass S j)
        (blockWords S B C ys hy j) := by
      simpa only [blockSublist,blockMass] using hs
    _ = _ := blockWords_mass S hV hS B C ys hy t
    _ = _ := by
      rw [poissonGraph_scaled h35 (Finset.univ \ S) B hB t _ ht hN,
        poissonGraph_scaled h35 S C hC t _ ht hN]

end ThLean.W.S340S

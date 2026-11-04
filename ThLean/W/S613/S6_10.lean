module

public import ThLean.BP.S6.Deletion

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S613

lemma degree_addPair_of_touches {n : ℕ} (G : Graph n) (e : Edge n) (a : Fin n)
    (ha : Touches a e.val) : degree (addPair G e) a = degree G a + 1 := by
  classical
  simp [degree, addPair, addEdge, Function.update]
  have hsplit (x : Sym2 (Fin n)) :
      (if Touches a x then if x = e.val then G e.val + 1 else G x else 0) =
        (if Touches a x then G x else 0) +
          (if Touches a x then if x = e.val then 1 else 0 else 0) := by
    by_cases hx : x = e.val
    · subst x
      simp [ha]
    · simp [hx]
  simp_rw [hsplit, Finset.sum_add_distrib]
  congr 1
  have hsum :
      (∑ x : Sym2 (Fin n), if Touches a x then if x = e.val then 1 else 0 else 0) =
        ∑ x, if x = e.val then if Touches a x then 1 else 0 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = e.val <;> simp [hx]
  rw [hsum]
  simp [ha]

lemma indicator_mono {P Q : Prop} (h : P → Q) : indicator P ≤ indicator Q := by
  unfold indicator
  split_ifs with hp hq
  · norm_num
  · exact False.elim (hq (h hp))
  · norm_num
  · norm_num

lemma indicator_and (P Q : Prop) : indicator (P ∧ Q) = indicator P * indicator Q := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [indicator, hp, hq]

lemma uniformMean_mono_of_nonempty {A : Type} [Fintype A] [Nonempty A]
    (f g : A → ℝ) (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  have hs : (∑ a, f a) ≤ ∑ a, g a := Finset.sum_le_sum fun a _ => h a
  have hc : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty A›
  exact (div_le_div_iff_of_pos_right hc).2 hs

lemma edge_nonempty {n : ℕ} (hn : 3 ≤ n) : Nonempty (Edge n) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    norm_num at this
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hv
  apply hab
  apply Sym2.mk_isDiag_iff.mp
  rw [hv]
  exact Sym2.diag_isDiag v

lemma nonpivotalDeletionCount_le_endpointSum (n q j : ℕ) (G : Graph n) (e : Edge n) :
    nonpivotalDeletionCount q j G e ≤
      ∑ a : Fin n, ∑ v : Fin n,
        indicator (Touches a e.val ∧ a ≠ v ∧ Frozen q G a v ∧ degree G a = j - 1) := by
  classical
  unfold nonpivotalDeletionCount
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro v _
  apply indicator_mono
  intro h
  rcases h with ⟨ht, hav, hfa, hfg, hd⟩
  refine ⟨ht, hav, hfg, ?_⟩
  have heq := degree_addPair_of_touches G e a ht
  rw [heq] at hd
  omega

theorem S6_10Statement_of_deps (h03 : ThLean.BP.S6.S6_03Statement) :
    ThLean.BP.S6.S6_10Statement := by
  classical
  intro n q j hn hq hj G
  let z : Fin n → ℝ := fun a =>
    ∑ v : Fin n, indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j - 1)
  have hmean := @uniformMean_mono_of_nonempty (Edge n) inferInstance (edge_nonempty hn)
    (fun e : Edge n => nonpivotalDeletionCount q j G e)
    (fun e : Edge n => ∑ a : Fin n, indicator (Touches a e.val) * z a)
    (by
      intro e
      have hp := nonpivotalDeletionCount_le_endpointSum n q j G e
      unfold z
      calc
        nonpivotalDeletionCount q j G e ≤
            ∑ a : Fin n, ∑ v : Fin n,
              indicator (Touches a e.val ∧ a ≠ v ∧ Frozen q G a v ∧ degree G a = j - 1) := hp
        _ = ∑ a : Fin n, indicator (Touches a e.val) *
              (∑ v : Fin n, indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j - 1)) := by
              calc
                _ = ∑ a : Fin n, ∑ v : Fin n,
                      indicator (Touches a e.val) *
                        indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j - 1) := by
                      simp_rw [indicator_and]
                _ = _ := by simp_rw [← Finset.mul_sum])
  have hpoint := h03 n hn |>.1 z
  rw [show z = fun a => ∑ v : Fin n,
    indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j - 1) by rfl] at hpoint
  have hmean' : uniformMean (fun e : Edge n =>
      ∑ a : Fin n, indicator (Touches a e.val) * z a) =
      (2 / (n : ℝ)) * ∑ a : Fin n, z a := hpoint
  change uniformMean (nonpivotalDeletionCount q j G) ≤ _
  rw [hmean'] at hmean
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold kappaDegree
  simp only [Fintype.card_fin]
  change uniformMean (nonpivotalDeletionCount q j G) ≤
    (2 / (n : ℝ)) * n * ((n : ℝ) - 1) *
      ((∑ a : Fin n, ∑ v : Fin n,
        indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j - 1)) /
        ((n : ℝ) * ((n : ℝ) - 1)))
  have hsum : ∑ a : Fin n, z a =
      ∑ a : Fin n, ∑ v : Fin n,
        indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j - 1) := by
    simp [z]
  rw [hsum]
  calc
    uniformMean (nonpivotalDeletionCount q j G) ≤
        (2 / (n : ℝ)) * ∑ a : Fin n, z a := hmean
    _ = _ := by
      rw [hsum]
      field_simp [ne_of_gt hn0, ne_of_gt hn1]

end ThLean.W.S613

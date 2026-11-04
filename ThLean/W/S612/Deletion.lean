module

public import ThLean.BP.S6.Deletion

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S6

namespace ThLean.W.S612

private lemma tupleGraph_occurrence_pos {n m : ℕ} (x : Hist n m) (i : Fin m) :
    0 < tupleGraph x (x i).val := by
  dsimp [tupleGraph]
  apply Finset.card_pos.mpr
  exact ⟨i, by simp⟩

attribute [local instance] Classical.propDecidable

private lemma indicator_mono_of_imp {p q : Prop} (h : p → q) :
    indicator p ≤ indicator q := by
  classical
  by_cases hp : p
  · have hq : q := h hp
    simp [indicator, hp, hq]
  · by_cases hq : q <;> simp [indicator, hp, hq]

private lemma restore_deleted_occurrence {n : ℕ} (G : Graph n) (e : Edge n)
    (h : 0 < G e.val) : addPair (erasePair G e) e = G := by
  funext f
  by_cases hf : f = e.val
  · subst f
    simp [addPair, erasePair, addEdge, eraseEdge, Function.update,
      Nat.sub_add_cancel (by omega : 1 ≤ G e.val)]
  · simp [addPair, erasePair, addEdge, eraseEdge, Function.update, hf]

private lemma nonpivotal_count_as_indices {n m q : ℕ} (x : Hist n m)
    (a v : Fin n) :
    nonpivotalCount q (tupleGraph x) a v =
      ∑ i : Fin m, if Touches a (x i).val ∧ Frozen q (tupleGraph x) a v ∧
        Frozen q (erasePair (tupleGraph x) (x i)) a v then 1 else 0 := by
  classical
  unfold nonpivotalCount
  let P (e : Sym2 (Fin n)) := Touches a e ∧ Frozen q (tupleGraph x) a v ∧
    Frozen q (eraseEdge (tupleGraph x) e) a v
  calc
    (∑ e : Sym2 (Fin n), if P e then tupleGraph x e else 0) =
        ∑ e : Sym2 (Fin n), if P e then
          (Finset.univ.filter (fun i : Fin m => (x i).val = e)).card else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hp : P e <;> simp [P, hp, tupleGraph]
    _ = ∑ e : Sym2 (Fin n), ∑ i : Fin m,
        if P e ∧ (x i).val = e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.card_filter]
      by_cases hp : P e <;> simp [P, hp]
    _ = ∑ i : Fin m, ∑ e : Sym2 (Fin n),
        if P e ∧ (x i).val = e then 1 else 0 := by
      exact Finset.sum_comm
    _ = ∑ i : Fin m, if P ((x i).val) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hp : P ((x i).val)
      · rw [Finset.sum_eq_single ((x i).val)]
        · simp [hp]
        · intro e he hne
          simp [eq_comm, hne]
        · simp
      · have hzero : ∀ e : Sym2 (Fin n),
            (if P e ∧ (x i).val = e then 1 else 0) = 0 := by
          intro e
          by_cases he : (x i).val = e
          · subst e
            simp [hp]
          · simp [he]
        simp [hp, hzero]
    _ = ∑ i : Fin m, if Touches a (x i).val ∧ Frozen q (tupleGraph x) a v ∧
        Frozen q (erasePair (tupleGraph x) (x i)) a v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases ht : Touches a (x i).val ∧ Frozen q (tupleGraph x) a v ∧
          Frozen q (eraseEdge (tupleGraph x) (x i).val) a v <;>
        simp [P, erasePair, ht]

theorem S6_09Statement_holds : ThLean.BP.S6.S6_09Statement := by
  intro n q m j K hn hq hm hj hK x
  let G : Graph n := tupleGraph x
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hn0 hn1
  have hbase :
      (K : ℝ) * (∑ a : Fin n, ∑ v : Fin n,
        indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j ∧
          K ≤ nonpivotalCount q G a v)) ≤
      ∑ i : Fin m, nonpivotalDeletionCount q j
        (erasePair G (x i)) (x i) := by
    calc
      (K : ℝ) * (∑ a : Fin n, ∑ v : Fin n,
          indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j ∧
            K ≤ nonpivotalCount q G a v))
          = ∑ a : Fin n, ∑ v : Fin n,
              (K : ℝ) * indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j ∧
                K ≤ nonpivotalCount q G a v) := by simp [Finset.mul_sum]
      _ ≤ ∑ a : Fin n, ∑ v : Fin n, ∑ i : Fin m,
          indicator (Touches a (x i).val ∧ a ≠ v ∧
            Frozen q (addPair (erasePair G (x i)) (x i)) a v ∧
            Frozen q (erasePair G (x i)) a v ∧
            degree (addPair (erasePair G (x i)) (x i)) a = j) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro v hv
        let P : Prop := a ≠ v ∧ Frozen q G a v ∧ degree G a = j ∧
          K ≤ nonpivotalCount q G a v
        classical
        by_cases hp : P
        · have hcount :
              (K : ℝ) ≤ ∑ i : Fin m,
                indicator (Touches a (x i).val ∧ Frozen q G a v ∧
                  Frozen q (erasePair G (x i)) a v) := by
            have hnat := hp.2.2.2
            have hcountNat : K ≤ ∑ i : Fin m,
                if Touches a (x i).val ∧ Frozen q G a v ∧
                  Frozen q (erasePair G (x i)) a v then 1 else 0 := by
              rw [← nonpivotal_count_as_indices]
              exact hnat
            have hcountCard : K ≤ (Finset.univ.filter (fun i : Fin m =>
                Touches a (x i).val ∧ Frozen q G a v ∧
                  Frozen q (erasePair G (x i)) a v)).card := by
              rw [Finset.card_filter]
              simpa using hcountNat
            have hcard : ((Finset.univ.filter (fun i : Fin m =>
                Touches a (x i).val ∧ Frozen q G a v ∧
                  Frozen q (erasePair G (x i)) a v)).card : ℝ) =
                ∑ i : Fin m, indicator (Touches a (x i).val ∧ Frozen q G a v ∧
                  Frozen q (erasePair G (x i)) a v) := by
              rw [Finset.card_filter]
              simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
                indicator]
              apply Finset.sum_congr rfl
              intro i hi
              by_cases htest : Touches a (x i).val ∧ Frozen q G a v ∧
                  Frozen q (erasePair G (x i)) a v <;>
                simp [htest]
            rw [← hcard]
            exact_mod_cast hcountCard
          have himp (i : Fin m)
              (hi : Touches a (x i).val ∧ Frozen q G a v ∧
                Frozen q (erasePair G (x i)) a v) :
              Touches a (x i).val ∧ a ≠ v ∧
                Frozen q (addPair (erasePair G (x i)) (x i)) a v ∧
                Frozen q (erasePair G (x i)) a v ∧
                degree (addPair (erasePair G (x i)) (x i)) a = j := by
            have hrestore := restore_deleted_occurrence G (x i) (by
              simpa [G] using tupleGraph_occurrence_pos x i)
            refine ⟨hi.1, hp.1, ?_, hi.2.2, ?_⟩
            · simpa [hrestore] using hi.2.1
            · simpa [hrestore] using hp.2.2.1
          have hsum :
              (∑ i : Fin m,
                indicator (Touches a (x i).val ∧ Frozen q G a v ∧
                  Frozen q (erasePair G (x i)) a v)) ≤
              ∑ i : Fin m,
                indicator (Touches a (x i).val ∧ a ≠ v ∧
                  Frozen q (addPair (erasePair G (x i)) (x i)) a v ∧
                  Frozen q (erasePair G (x i)) a v ∧
                  degree (addPair (erasePair G (x i)) (x i)) a = j) := by
            apply Finset.sum_le_sum
            intro i hi
            exact indicator_mono_of_imp (himp i)
          have htotal := hcount.trans hsum
          simpa [P, indicator, hp] using htotal
        · have hnonneg : 0 ≤ ∑ i : Fin m,
              indicator (Touches a (x i).val ∧ a ≠ v ∧
                Frozen q (addPair (erasePair G (x i)) (x i)) a v ∧
                Frozen q (erasePair G (x i)) a v ∧
                degree (addPair (erasePair G (x i)) (x i)) a = j) :=
            Finset.sum_nonneg fun i _ => by
              by_cases hH : Touches a (x i).val ∧ a ≠ v ∧
                  Frozen q (addPair (erasePair G (x i)) (x i)) a v ∧
                  Frozen q (erasePair G (x i)) a v ∧
                  degree (addPair (erasePair G (x i)) (x i)) a = j <;>
                simp [indicator, hH]
          simpa [P, indicator, hp] using hnonneg
      _ = ∑ i : Fin m, nonpivotalDeletionCount q j
          (erasePair G (x i)) (x i) := by
        calc
          _ = ∑ a : Fin n, ∑ i : Fin m, ∑ v : Fin n,
              indicator (Touches a (x i).val ∧ a ≠ v ∧
                Frozen q (addPair (erasePair G (x i)) (x i)) a v ∧
                Frozen q (erasePair G (x i)) a v ∧
                degree (addPair (erasePair G (x i)) (x i)) a = j) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact Finset.sum_comm
          _ = ∑ i : Fin m, ∑ a : Fin n, ∑ v : Fin n,
              indicator (Touches a (x i).val ∧ a ≠ v ∧
                Frozen q (addPair (erasePair G (x i)) (x i)) a v ∧
                Frozen q (erasePair G (x i)) a v ∧
                degree (addPair (erasePair G (x i)) (x i)) a = j) := by
            exact Finset.sum_comm
          _ = ∑ i : Fin m, nonpivotalDeletionCount q j
              (erasePair G (x i)) (x i) := by rfl
  have hrewrite :
      (K : ℝ) * (n : ℝ) * ((n : ℝ) - 1) *
          kappaDegreeNP q K j G =
        (K : ℝ) * (∑ a : Fin n, ∑ v : Fin n,
          indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j ∧
            K ≤ nonpivotalCount q G a v)) := by
    unfold kappaDegreeNP
    simp only [Fintype.card_fin]
    field_simp [ne_of_gt hden]
  rw [hrewrite]
  exact hbase

end ThLean.W.S612

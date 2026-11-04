module

public import ThLean.BP.S6.Deletion

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S614

private lemma historyEdge_pos {n m : ℕ} (x : EdgeTuple (Fin n) m) (i : Fin m) :
    0 < tupleGraph x (x i).val := by
  classical
  unfold tupleGraph
  apply Finset.card_pos.mpr
  exact ⟨i, by simp⟩

private lemma erase_add_pair {n : ℕ} (G : MGraph (Fin n)) (e : Pair (Fin n))
    (he : 0 < G e.val) : addPair (erasePair G e) e = G := by
  classical
  ext f
  by_cases hf : f = e.val
  · subst f
    simp [addPair, erasePair, addEdge, eraseEdge, Function.update]
    omega
  · simp [addPair, erasePair, addEdge, eraseEdge, Function.update, hf]

private lemma history_indicator_count {n m : ℕ} (x : EdgeTuple (Fin n) m)
    (P : Sym2 (Fin n) → Prop) [DecidablePred P] :
    (∑ i : Fin m, indicator (P (x i).val)) =
      ∑ e : Sym2 (Fin n), if P e then (tupleGraph x e : ℝ) else 0 := by
  classical
  have hfib : (∑ e : Sym2 (Fin n), ∑ i : Fin m with (x i).val = e,
      indicator (P (x i).val)) = (∑ i : Fin m, indicator (P (x i).val)) := by
    simpa using (Finset.sum_fiberwise_eq_sum_filter (s := Finset.univ) (t := Finset.univ)
      (g := fun i : Fin m => (x i).val) (f := fun i => indicator (P (x i).val)))
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro e he
  calc
    (∑ i : Fin m with (x i).val = e, indicator (P (x i).val)) =
        ∑ i : Fin m with (x i).val = e, if P e then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          have hie : (x i).val = e := by simpa using hi
          by_cases hp : P e <;> simp [indicator, hp, hie]
    _ = if P e then ((Finset.univ.filter (fun i : Fin m => (x i).val = e)).card : ℝ) else 0 := by
      by_cases hp : P e
      · simp only [hp, ↓reduceIte]
        rw [Finset.sum_const]
        simp
      · simp [hp]
    _ = if P e then (tupleGraph x e : ℝ) else 0 := by simp [tupleGraph]

private lemma occurrence_edge_count {n : ℕ} (G : MGraph (Fin n))
    (P : Sym2 (Fin n) → Prop) [DecidablePred P] :
    ((Finset.univ.filter (fun o : Occurrence G => P o.1)).card : ℝ) =
      ∑ e : Sym2 (Fin n), if P e then (G e : ℝ) else 0 := by
  classical
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e he
  calc
    (∑ i : Fin (G e), if P ((⟨e, i⟩ : Occurrence G).1) then (1 : ℝ) else 0) =
        ∑ i : Fin (G e), if P e then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hp : P e <;> simp [hp]
    _ = if P e then (G e : ℝ) else 0 := by simp

theorem S6_12Statement_of_deps (h04b : ThLean.BP.S6.S6_04bStatement) :
    ThLean.BP.S6.S6_12Statement := by
  intro n q m j K hn hq hm hK hKj x
  let G : MGraph (Fin n) := tupleGraph x
  let c : ℝ := ((j - K + 1 : ℕ) : ℝ)
  let eligible (a v : Fin n) : Prop :=
    a ≠ v ∧ Frozen q G a v ∧ degree G a = j ∧ nonpivotalCount q G a v < K
  let pivotalOn (a v : Fin n) (e : Sym2 (Fin n)) : Prop :=
    Touches a e ∧ Frozen q G a v ∧ ¬ Frozen q (eraseEdge G e) a v
  let deletedOn (a v : Fin n) (i : Fin m) : Prop :=
    Touches a (x i).val ∧ a ≠ v ∧
      Frozen q (addPair (erasePair G (x i)) (x i)) a v ∧
      ¬ Frozen q (erasePair G (x i)) a v ∧
      degree (erasePair G (x i)) a = j - 1
  have hpiv (a v : Fin n) (he : eligible a v) :
      c ≤ ∑ i : Fin m, indicator (pivotalOn a v (x i).val) := by
    rcases he with ⟨hav, hfr, hd, hnp⟩
    have hncard := (h04b n q hn hq).1 G a v j K hav hfr hd hK hKj hnp
    have hfilter :
        (Finset.univ.filter (fun o : Occurrence G => Pivotal q G a v o)) =
          Finset.univ.filter (fun o : Occurrence G => pivotalOn a v o.1) := by
      ext o
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    have hreal : c ≤
        ((Finset.univ.filter (fun o : Occurrence G => pivotalOn a v o.1)).card : ℝ) := by
      change ((j - K + 1 : ℕ) : ℝ) ≤ _
      rw [← hfilter]
      exact_mod_cast hncard
    calc
      c ≤ ((Finset.univ.filter (fun o : Occurrence G => pivotalOn a v o.1)).card : ℝ) := hreal
      _ = ∑ e : Sym2 (Fin n), if pivotalOn a v e then (G e : ℝ) else 0 :=
        occurrence_edge_count G (pivotalOn a v)
      _ = ∑ i : Fin m, indicator (pivotalOn a v (x i).val) := by
        symm
        exact history_indicator_count x (pivotalOn a v)
  have hImp (a v : Fin n) (he : eligible a v) (i : Fin m) :
      pivotalOn a v (x i).val → deletedOn a v i := by
    intro h
    rcases he with ⟨hav, hfr, hd, hnp⟩
    rcases h with ⟨htouch, hFrozen, hnot⟩
    have hpos : 0 < G (x i).val := by
      simpa [G] using historyEdge_pos x i
    have hrec : addPair (erasePair G (x i)) (x i) = G := erase_add_pair G (x i) hpos
    rcases (h04b n q hn hq).2.2 G a (x i) hfr.1 hpos htouch with ⟨_, hdeg⟩
    have hdeg' : degree (erasePair G (x i)) a = j - 1 := by
      have hdiff : degree (erasePair G (x i)) a + 1 = j := by
        exact hdeg.trans hd
      omega
    have hFrozen' : Frozen q (addPair (erasePair G (x i)) (x i)) a v := by
      simpa [hrec] using hFrozen
    exact ⟨htouch, hav, hFrozen', hnot, hdeg'⟩
  have hpair (a v : Fin n) (he : eligible a v) :
      c ≤ ∑ i : Fin m, indicator (deletedOn a v i) := by
    have hsum : (∑ i : Fin m, indicator (pivotalOn a v (x i).val)) ≤
        ∑ i : Fin m, indicator (deletedOn a v i) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hp : pivotalOn a v (x i).val
      · have hd := hImp a v he i hp
        simp [indicator, hp, hd]
      · simp [indicator, hp]
        split_ifs <;> norm_num
    exact (hpiv a v he).trans hsum
  have hpoint (a v : Fin n) :
      c * indicator (eligible a v) ≤ ∑ i : Fin m, indicator (deletedOn a v i) := by
    by_cases he : eligible a v
    · simpa [indicator, he] using hpair a v he
    · simp only [indicator, he, ↓reduceIte, mul_zero]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> norm_num
  have hdouble :
      c * (∑ a : Fin n, ∑ v : Fin n, indicator (eligible a v)) ≤
        ∑ i : Fin m, ∑ a : Fin n, ∑ v : Fin n, indicator (deletedOn a v i) := by
    calc
      c * (∑ a : Fin n, ∑ v : Fin n, indicator (eligible a v)) =
          ∑ a : Fin n, ∑ v : Fin n, c * indicator (eligible a v) := by
            simp_rw [Finset.mul_sum]
      _ ≤ ∑ a : Fin n, ∑ v : Fin n, ∑ i : Fin m, indicator (deletedOn a v i) := by
            apply Finset.sum_le_sum
            intro a ha
            apply Finset.sum_le_sum
            intro v hv
            exact hpoint a v
      _ = ∑ a : Fin n, ∑ i : Fin m, ∑ v : Fin n, indicator (deletedOn a v i) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      _ = ∑ i : Fin m, ∑ a : Fin n, ∑ v : Fin n, indicator (deletedOn a v i) := by
            exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
  have hdouble' :
      c * (∑ a : Fin n, ∑ v : Fin n,
        indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j ∧
          nonpivotalCount q G a v < K)) ≤
        ∑ i : Fin m, pivotalDeletionCount q j (erasePair G (x i)) (x i) := by
    simpa [eligible, deletedOn, pivotalDeletionCount] using hdouble
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnR1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc
    ((j - K + 1 : ℕ) : ℝ) * n * ((n : ℝ) - 1) *
        kappaDegreePiv q K j G =
      c * (∑ a : Fin n, ∑ v : Fin n,
        indicator (a ≠ v ∧ Frozen q G a v ∧ degree G a = j ∧
          nonpivotalCount q G a v < K)) := by
        simp only [c, kappaDegreePiv, Fintype.card_fin]
        field_simp [ne_of_gt hnR, ne_of_gt hnR1]
    _ ≤ ∑ i : Fin m, pivotalDeletionCount q j (erasePair G (x i)) (x i) := hdouble'

end ThLean.W.S614

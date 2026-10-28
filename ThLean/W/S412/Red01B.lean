import ThLean.BP.S4.Deletion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S412

open ThresholdFoundations

private lemma deletedPrefix_update {n U : ℕ} (x : EdgeTuple (Fin n) U)
    (i : Fin U) (e : Pair (Fin n)) (m : ℕ) :
    deletedPrefix (Function.update x i e) i m = deletedPrefix x i m := by
  classical
  funext f
  unfold deletedPrefix
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hjm, hji, hx⟩
    refine ⟨hjm, hji, ?_⟩
    simpa [Function.update_apply, hji] using hx
  · rintro ⟨hjm, hji, hx⟩
    refine ⟨hjm, hji, ?_⟩
    simpa [Function.update_apply, hji] using hx

private lemma deletedPrefix_eq_prefix_of_le {n U : ℕ}
    (x : EdgeTuple (Fin n) U) (i : Fin U) {m : ℕ} (hm : m ≤ i.val) :
    deletedPrefix x i m = tuplePrefix x m := by
  classical
  funext f
  unfold deletedPrefix tuplePrefix
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hjm, hji, hx⟩
    exact ⟨hjm, hx⟩
  · rintro ⟨hjm, hx⟩
    have hji : j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      omega
    exact ⟨hjm, hji, hx⟩

private lemma deletedPrefix_subgraph {n U : ℕ}
    (x : EdgeTuple (Fin n) U) (i : Fin U) (m : ℕ) :
    subgraph (deletedPrefix x i m) (tuplePrefix x m) := by
  intro f
  unfold deletedPrefix tuplePrefix
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨hj.1, hj.2.2⟩

private lemma colorable_deletedPrefix_of_colorable_prefix {n U q : ℕ}
    (x : EdgeTuple (Fin n) U) (i : Fin U) (m : ℕ)
    (h : Colorable q (tuplePrefix x m)) : Colorable q (deletedPrefix x i m) := by
  rcases h with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro u v huv
  apply hσ u v
  exact lt_of_lt_of_le huv (deletedPrefix_subgraph x i m (s(u, v)))

private lemma deletion_indicator_diff {n U q : ℕ}
    (x : EdgeTuple (Fin n) U) (i : Fin U) (m : ℕ) :
    (if Colorable q (deletedPrefix x i m) then (1 : ℝ) else 0) -
        (if Colorable q (tuplePrefix x m) then 1 else 0) =
      if i.val < m then indicator (deletionDisagreement q x i m) else 0 := by
  classical
  by_cases him : i.val < m
  · by_cases hd : Colorable q (deletedPrefix x i m)
    · by_cases hp : Colorable q (tuplePrefix x m)
      · simp [deletionDisagreement, indicator, him, hd, hp]
      · simp [deletionDisagreement, indicator, him, hd, hp]
    · have hp : ¬ Colorable q (tuplePrefix x m) := by
        intro hp
        exact hd (colorable_deletedPrefix_of_colorable_prefix x i m hp)
      simp [deletionDisagreement, indicator, him, hd, hp]
  · have heq : deletedPrefix x i m = tuplePrefix x m :=
      deletedPrefix_eq_prefix_of_le x i (by omega)
    simp [him, heq]

private lemma deletionYMinus_diff_formula {n U q L : ℕ}
    (x : EdgeTuple (Fin n) U) (i : Fin U) :
    ((deletionYMinus q L i x : ℕ) : ℝ) - (deletionY q L x : ℝ) =
      ∑ m ∈ Finset.Icc (max (i.val + 1) (L + 1)) U,
        indicator (deletionDisagreement q x i m) := by
  classical
  let S := Finset.Icc (L + 1) U
  have hfilter : S.filter (fun m => i.val < m) =
      Finset.Icc (max (i.val + 1) (L + 1)) U := by
    ext m
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    omega
  calc
    ((deletionYMinus q L i x : ℕ) : ℝ) - (deletionY q L x : ℝ) =
        ∑ m ∈ S,
          ((if Colorable q (deletedPrefix x i m) then (1 : ℝ) else 0) -
            (if Colorable q (tuplePrefix x m) then 1 else 0)) := by
      simp only [deletionYMinus, deletionY, S, Nat.cast_add, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    _ = ∑ m ∈ S, if i.val < m then
          indicator (deletionDisagreement q x i m) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      exact deletion_indicator_diff x i m
    _ = ∑ m ∈ Finset.Icc (max (i.val + 1) (L + 1)) U,
          indicator (deletionDisagreement q x i m) := by
      rw [← Finset.sum_filter, hfilter]

private lemma indicator_real_bounds (P : Prop) :
    0 ≤ indicator P ∧ indicator P ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

theorem S4_RED_01BStatement_holds : ThLean.BP.S4.S4_RED_01BStatement := by
  classical
  intro q n hq hn L U hLU
  refine ⟨?_, ?_, ?_⟩
  · intro i x e
    unfold deletionYMinus
    apply congrArg (fun z : ℕ => L + z)
    apply Finset.sum_congr rfl
    intro m hm
    rw [deletedPrefix_update]
  · intro i x
    exact deletionYMinus_diff_formula x i
  · intro i x
    rw [deletionYMinus_diff_formula]
    let R := Finset.Icc (max (i.val + 1) (L + 1)) U
    have hsubset : R ⊆ Finset.Icc (L + 1) U := by
      intro m hm
      simp only [R, Finset.mem_Icc] at hm ⊢
      exact ⟨le_trans (Nat.le_max_right _ _) hm.1, hm.2⟩
    have hcard : (Finset.Icc (L + 1) U).card = U - L := by
      simp
    have hsum_nonneg : 0 ≤ ∑ m ∈ R, indicator (deletionDisagreement q x i m) :=
      Finset.sum_nonneg fun m hm => (indicator_real_bounds _).1
    have hsum_le :
        (∑ m ∈ R, indicator (deletionDisagreement q x i m)) ≤ (U : ℝ) - L := by
      calc
        (∑ m ∈ R, indicator (deletionDisagreement q x i m)) ≤
            ∑ _m ∈ R, (1 : ℝ) :=
          Finset.sum_le_sum fun m hm => (indicator_real_bounds _).2
        _ = (R.card : ℝ) := by simp
        _ ≤ ((Finset.Icc (L + 1) U).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset
        _ = (U : ℝ) - L := by rw [hcard]; norm_cast
    exact ⟨hsum_nonneg, hsum_le⟩

end ThLean.W.S412

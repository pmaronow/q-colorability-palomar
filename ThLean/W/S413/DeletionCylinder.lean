import ThLean.BP.S4.Deletion
import ThLean.BP.S4.Finite

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S413
open ThresholdFoundations

private theorem uniformMean_fintype_irrel {A : Type*} (I J : Fintype A) (f : A → ℝ) :
    @uniformMean A I f = @uniformMean A J f := by
  cases Subsingleton.elim I J
  rfl

private theorem tuplePrefix_restrict {V : Type*} [Fintype V]
    {U M : ℕ} (hUM : U ≤ M) (x : EdgeTuple V M) {m : ℕ} (hm : m ≤ U) :
    tuplePrefix (restrictTuple hUM x) m = tuplePrefix x m := by
  classical
  funext e
  unfold tuplePrefix
  let s : Finset (Fin U) := Finset.univ.filter (fun j =>
    j.val < m ∧ (restrictTuple hUM x j).val = e)
  let t : Finset (Fin M) := Finset.univ.filter (fun j =>
    j.val < m ∧ (x j).val = e)
  change s.card = t.card
  refine Finset.card_bij (s := s) (t := t)
    (fun j _ => ⟨j.val, by omega⟩) ?_ ?_ ?_
  · intro j hj
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hj.1
    · simpa [restrictTuple] using hj.2
  · intro j₁ hj₁ j₂ hj₂ heq
    apply Fin.ext
    simpa using congrArg Fin.val heq
  · intro j hj
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
    · simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact hj.1
      · change (x ⟨j.val, by omega⟩).val = e
        have hidx : (⟨j.val, by omega⟩ : Fin M) = j := Fin.ext rfl
        rw [hidx]
        exact hj.2
    · apply Fin.ext
      rfl

private theorem deletedPrefix_restrict {V : Type*} [Fintype V]
    {U M : ℕ} (hUM : U ≤ M) (i : Fin U) (x : EdgeTuple V M)
    {m : ℕ} (hm : m ≤ U) :
    deletedPrefix x ⟨i.val, lt_of_lt_of_le i.isLt hUM⟩ m =
      deletedPrefix (restrictTuple hUM x) i m := by
  classical
  funext e
  unfold deletedPrefix
  let iM : Fin M := ⟨i.val, lt_of_lt_of_le i.isLt hUM⟩
  let s : Finset (Fin U) := Finset.univ.filter (fun j =>
    j.val < m ∧ j ≠ i ∧ (restrictTuple hUM x j).val = e)
  let t : Finset (Fin M) := Finset.univ.filter (fun j =>
    j.val < m ∧ j ≠ iM ∧ (x j).val = e)
  change t.card = s.card
  symm
  have hne (j : Fin U) (hjm : j.val < m) :
      (⟨j.val, lt_of_lt_of_le hjm (le_trans hm hUM)⟩ : Fin M) ≠ iM ↔ j ≠ i := by
    constructor
    · intro hne hj
      apply hne
      apply Fin.ext
      simpa [iM] using congrArg Fin.val hj
    · intro hne hj
      apply hne
      apply Fin.ext
      simpa [iM] using congrArg Fin.val hj
  refine Finset.card_bij (s := s) (t := t)
    (fun j _ => ⟨j.val, by omega⟩) ?_ ?_ ?_
  · intro j hj
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hj.1, ?_, ?_⟩
    · exact (hne j hj.1).2 hj.2.1
    · simpa [restrictTuple] using hj.2.2
  · intro j₁ hj₁ j₂ hj₂ heq
    apply Fin.ext
    simpa using congrArg Fin.val heq
  · intro j hj
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    let jU : Fin U := ⟨j.val, by omega⟩
    refine ⟨jU, ?_, ?_⟩
    · simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hj.1, ?_, ?_⟩
      · exact (hne jU hj.1).1 hj.2.1
      · change (x ⟨j.val, by omega⟩).val = e
        have hidx : (⟨j.val, by omega⟩ : Fin M) = j := Fin.ext rfl
        rw [hidx]
        exact hj.2.2
    · apply Fin.ext
      rfl

theorem S4_RED_01CStatement_of_deps
    (ha : ThLean.BP.S4.S4_RED_01AStatement)
    (hpre : ThresholdFoundations.PreFiniteLawsStatement.{0,0}) :
    ThLean.BP.S4.S4_RED_01CStatement := by
  intro q n hq hn M L U hLU hUM
  have hcard : 2 ≤ Fintype.card (Fin n) := by simp; omega
  constructor
  · intro f
    let g : EdgeTuple (Fin n) U → ℝ := fun y => f (deletionY q L y)
    have hpoint : ∀ x : EdgeTuple (Fin n) M,
        f (clippedLast q L U x) = g (restrictTuple hUM x) := by
      intro x
      dsimp [g]
      rw [ha q n hq hn M L U hLU hUM x]
      unfold deletionY
      congr 2
      apply Finset.sum_congr rfl
      intro m hm
      have hmU : m ≤ U := (Finset.mem_Icc.mp hm).2
      rw [tuplePrefix_restrict hUM x hmU]
    calc
      uniformMean (fun x : EdgeTuple (Fin n) M => f (clippedLast q L U x)) =
          uniformMean (fun x : EdgeTuple (Fin n) M => g (restrictTuple hUM x)) := by
            apply congrArg uniformMean
            funext x
            exact hpoint x
      _ = uniformMean g := by
        convert hpre.2.2.1 (Fin n) hcard U M hUM g using 1
        all_goals exact uniformMean_fintype_irrel _ _ _
      _ = uniformMean (fun y : EdgeTuple (Fin n) U => f (deletionY q L y)) := rfl
  · intro i f
    let g : EdgeTuple (Fin n) U → ℝ := fun y =>
      f (deletionY q L y) (deletionYMinus q L i y)
    have hpoint : ∀ x : EdgeTuple (Fin n) M,
        f (clippedLast q L U x)
            (L + ∑ m ∈ Finset.Icc (L+1) U,
              if Colorable q (deletedPrefix x ⟨i.val, lt_of_lt_of_le i.isLt hUM⟩ m)
              then 1 else 0) = g (restrictTuple hUM x) := by
      intro x
      dsimp [g]
      rw [ha q n hq hn M L U hLU hUM x]
      unfold deletionY deletionYMinus
      have hfirst :
          (∑ m ∈ Finset.Icc (L+1) U,
            if Colorable q (tuplePrefix x m) then 1 else 0) =
          (∑ m ∈ Finset.Icc (L+1) U,
            if Colorable q (tuplePrefix (restrictTuple hUM x) m) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [tuplePrefix_restrict hUM x ((Finset.mem_Icc.mp hm).2)]
      rw [hfirst]
      apply congrArg (fun z : ℕ => f
        (L + ∑ m ∈ Finset.Icc (L+1) U,
          if Colorable q (tuplePrefix (restrictTuple hUM x) m) then 1 else 0) z)
      apply congrArg (fun z : ℕ => L + z)
      apply Finset.sum_congr rfl
      intro m hm
      rw [deletedPrefix_restrict hUM i x ((Finset.mem_Icc.mp hm).2)]
    calc
      uniformMean (fun x : EdgeTuple (Fin n) M =>
          f (clippedLast q L U x)
            (L + ∑ m ∈ Finset.Icc (L+1) U,
              if Colorable q (deletedPrefix x ⟨i.val, lt_of_lt_of_le i.isLt hUM⟩ m)
              then 1 else 0)) =
          uniformMean (fun x : EdgeTuple (Fin n) M => g (restrictTuple hUM x)) := by
            apply congrArg uniformMean
            funext x
            exact hpoint x
      _ = uniformMean g := by
        convert hpre.2.2.1 (Fin n) hcard U M hUM g using 1
        all_goals exact uniformMean_fintype_irrel _ _ _
      _ = uniformMean (fun y : EdgeTuple (Fin n) U =>
          f (deletionY q L y) (deletionYMinus q L i y)) := rfl

end ThLean.W.S413

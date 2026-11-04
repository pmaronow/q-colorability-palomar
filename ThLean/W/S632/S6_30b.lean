module

public import ThLean.BP.S6.Potential

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S632

private theorem firstFailure_le_iff {P : ℕ → Prop}
    (hmono : ∀ a b, a ≤ b → P a → P b) (m : ℕ) :
    firstFailure P ≤ (m : WithTop ℕ) ↔ P m := by
  classical
  unfold firstFailure
  by_cases hex : ∃ k, P k
  · simp only [dif_pos hex]
    constructor
    · intro hle
      have hle' : Nat.find hex ≤ m := by exact_mod_cast hle
      exact hmono (Nat.find hex) m hle' (Nat.find_spec hex)
    · intro hp
      exact_mod_cast (Nat.find_min' hex hp)
  · have hnot : ¬ P m := by
      intro hp
      exact hex ⟨m, hp⟩
    simp [hex, hnot]

private theorem tuplePrefix_mono {n M : ℕ} (x : EdgeTuple (Fin n) M) {a b : ℕ}
    (hab : a ≤ b) (u : Fin n) :
    degree (tuplePrefix x a) u ≤ degree (tuplePrefix x b) u := by
  classical
  have hgraph (e : Sym2 (Fin n)) : tuplePrefix x a e ≤ tuplePrefix x b e := by
    unfold tuplePrefix
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨lt_of_lt_of_le hi.1 hab, hi.2⟩
  unfold degree
  apply Finset.sum_le_sum
  intro e he
  by_cases ht : Touches u e <;> simp [ht, hgraph e]

private theorem processGraph_mono {n : ℕ} (ω : EdgeStream (Fin n))
    {a b : ℕ} (hab : a ≤ b) (e : Sym2 (Fin n)) :
    processGraph ω a e ≤ processGraph ω b e := by
  classical
  unfold processGraph tupleGraph
  apply Finset.card_le_card_of_injOn (fun i : Fin a => i.castLE hab)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa using hi
  · intro i hi j hj hij
    apply Fin.ext
    simpa using congrArg Fin.val hij

private theorem degree_processGraph_mono {n : ℕ} (ω : EdgeStream (Fin n))
    {a b : ℕ} (hab : a ≤ b) (u : Fin n) :
    degree (processGraph ω a) u ≤ degree (processGraph ω b) u := by
  unfold degree
  apply Finset.sum_le_sum
  intro e he
  by_cases ht : Touches u e <;> simp [ht, processGraph_mono ω hab e]

private theorem tuplePrefix_eq_of_agree {n M : ℕ} (x y : EdgeTuple (Fin n) M)
    (m : ℕ) (hxy : ∀ i : Fin M, i.val < m → x i = y i) :
    tuplePrefix x m = tuplePrefix y m := by
  classical
  funext e
  unfold tuplePrefix
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨him, hie⟩
    refine ⟨him, ?_⟩
    calc
      (y i).val = (x i).val := congrArg Subtype.val (hxy i him).symm
      _ = e := hie
  · rintro ⟨him, hie⟩
    refine ⟨him, ?_⟩
    calc
      (x i).val = (y i).val := congrArg Subtype.val (hxy i him)
      _ = e := hie

private theorem processGraph_eq_of_agree {n : ℕ} (ω ω' : EdgeStream (Fin n))
    (m : ℕ) (hω : AgreeUpTo m ω ω') :
    processGraph ω m = processGraph ω' m := by
  classical
  funext e
  unfold processGraph tupleGraph
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hie
    calc
      (ω' i.val).val = (ω i.val).val := congrArg Subtype.val (hω i.val i.isLt).symm
      _ = e := hie
  · intro hie
    calc
      (ω i.val).val = (ω' i.val).val := congrArg Subtype.val (hω i.val i.isLt)
      _ = e := hie

private theorem degreeStart_le_iff {n M : ℕ} (u : Fin n) (j m : ℕ)
    (x : EdgeTuple (Fin n) M) :
    ThLean.BP.S6.degreeStart u j x ≤ (m : WithTop ℕ) ↔
      j ≤ degree (tuplePrefix x m) u := by
  unfold ThLean.BP.S6.degreeStart
  apply firstFailure_le_iff
  intro a b hab ha
  exact ha.trans (tuplePrefix_mono x hab u)

private theorem degreeHittingTime_le_iff {n : ℕ} (u : Fin n) (j m : ℕ)
    (ω : EdgeStream (Fin n)) :
    degreeHittingTime u j ω ≤ (m : WithTop ℕ) ↔
      j ≤ degree (processGraph ω m) u := by
  unfold degreeHittingTime
  apply firstFailure_le_iff
  intro a b hab ha
  exact ha.trans (degree_processGraph_mono ω hab u)

theorem S6_30bStatement_holds : ThLean.BP.S6.S6_30bStatement := by
  intro n q M j hn hq hj u
  constructor
  · intro m x y hxy
    rw [degreeStart_le_iff u j m x, degreeStart_le_iff u j m y]
    rw [tuplePrefix_eq_of_agree x y m hxy]
  constructor
  · intro x m
    exact degreeStart_le_iff u j m x
  constructor
  · intro x hactive
    have hstopM : finiteStoppedTime q x ≤ M := Nat.min_le_right _ _
    have hless : ThLean.BP.S6.degreeStart u j x < (M : WithTop ℕ) :=
      lt_of_lt_of_le hactive (by exact_mod_cast hstopM)
    have hM : 1 ≤ M := by
      by_contra hnot
      have hzero : M = 0 := by omega
      subst M
      have hge : (0 : WithTop ℕ) ≤ ThLean.BP.S6.degreeStart u j x := bot_le
      exact (not_lt_of_ge hge) hless
    have hex : ∃ k : ℕ, ThLean.BP.S6.degreeStart u j x = (k : WithTop ℕ) := by
      cases htime : ThLean.BP.S6.degreeStart u j x with
      | top => simp [htime] at hless
      | coe k => exact ⟨k, rfl⟩
    obtain ⟨k, hk⟩ := hex
    have hkM : k < M := by
      rw [hk] at hless
      exact WithTop.coe_lt_coe.mp hless
    have hkle : ThLean.BP.S6.degreeStart u j x ≤ ((M - 1 : ℕ) : WithTop ℕ) := by
      rw [hk]
      exact_mod_cast (show k ≤ M - 1 by omega)
    exact ⟨hM, (degreeStart_le_iff u j (M - 1) x).mp hkle⟩
  constructor
  · intro m ω ω' hagree
    change (degreeHittingTime u j ω ≤ (m : WithTop ℕ)) ↔
      (degreeHittingTime u j ω' ≤ (m : WithTop ℕ))
    rw [degreeHittingTime_le_iff u j m ω, degreeHittingTime_le_iff u j m ω']
    rw [processGraph_eq_of_agree ω ω' m hagree]
  · intro ω m
    exact degreeHittingTime_le_iff u j m ω

end ThLean.W.S632

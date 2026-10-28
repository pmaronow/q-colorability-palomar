import ThLean.BP.S3.Adapters

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S394

open ThresholdFoundations

private lemma tupleGraph_prefix_mono {V : Type*} [Fintype V]
    (ω : EdgeStream V) {m n : ℕ} (hmn : m ≤ n) (e : Sym2 V) :
    processGraph ω m e ≤ processGraph ω n e := by
  unfold processGraph tupleGraph
  apply Finset.card_le_card_of_injOn (fun i : Fin m => Fin.castLE hmn i)
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa using hi
  · intro i hi j hj hij
    apply Fin.ext
    simpa using congrArg Fin.val hij

private lemma degree_mono {V : Type*} [Fintype V] {G H : MGraph V}
    (hGH : ∀ e, G e ≤ H e) (u : V) : degree G u ≤ degree H u := by
  unfold degree
  apply Finset.sum_le_sum
  intro e he
  by_cases ht : Touches u e
  · simp [ht, hGH]
  · simp [ht]

private lemma degree_process_mono {V : Type*} [Fintype V]
    (ω : EdgeStream V) {m n : ℕ} (hmn : m ≤ n) (u : V) :
    degree (processGraph ω m) u ≤ degree (processGraph ω n) u := by
  apply degree_mono (fun e => tupleGraph_prefix_mono ω hmn e)

private lemma firstFailure_le_iff {P : ℕ → Prop}
    (hmono : ∀ k l, k ≤ l → P k → P l) (m : ℕ) :
    firstFailure P ≤ (m : WithTop ℕ) ↔ P m := by
  unfold firstFailure
  by_cases h : ∃ k, P k
  · simp only [dif_pos h]
    constructor
    · intro ht
      apply hmono (Nat.find h) m
      · exact (WithTop.coe_le_coe.mp ht)
      · exact Nat.find_spec h
    · intro hm
      exact WithTop.coe_le_coe.mpr (Nat.find_min' h hm)
  · have hPm : ¬ P m := by
      intro hm
      exact h ⟨m, hm⟩
    simp [h, hPm]

private def finiteExtension {V : Type*} {M : ℕ} (p : Pair V)
    (x : EdgeTuple V M) : EdgeStream V :=
  fun i => if hi : i < M then x ⟨i, hi⟩ else p

private lemma min_coe_le_iff {m M : ℕ} (hm : m < M) (z : WithTop ℕ) :
    min z (M : WithTop ℕ) ≤ (m : WithTop ℕ) ↔ z ≤ (m : WithTop ℕ) := by
  rw [min_le_iff]
  constructor
  · rintro (hz | hM)
    · exact hz
    · exact False.elim ((not_le_of_gt (WithTop.coe_lt_coe.mpr hm)) hM)
  · intro hz
    exact Or.inl hz

private lemma min_stopping_invariant {V : Type*} [Fintype V] {M : ℕ}
    (T : EdgeStream V → WithTop ℕ) (hT : IsStoppingTime T)
    {ω ω' : EdgeStream V} (hag : AgreeUpTo M ω ω') :
    min (T ω) (M : WithTop ℕ) = min (T ω') (M : WithTop ℕ) := by
  have hle : min (T ω) (M : WithTop ℕ) ≤ min (T ω') (M : WithTop ℕ) := by
    by_contra hnot
    have hlt : min (T ω') (M : WithTop ℕ) < min (T ω) (M : WithTop ℕ) := lt_of_not_ge hnot
    have hboundLeft : min (T ω) (M : WithTop ℕ) ≤ (M : WithTop ℕ) := min_le_right _ _
    have hboundRight : min (T ω') (M : WithTop ℕ) ≤ (M : WithTop ℕ) := min_le_right _ _
    cases hz : min (T ω') (M : WithTop ℕ) with
    | top =>
        have htop : (⊤ : WithTop ℕ) ≤ (M : WithTop ℕ) := by
          rw [← hz]
          exact hboundRight
        exact (by simpa using htop)
    | coe k =>
        have hkM : k < M := by
          have hkm : (k : WithTop ℕ) < (M : WithTop ℕ) := by
            simpa [hz] using lt_of_lt_of_le hlt hboundLeft
          exact WithTop.coe_lt_coe.mp hkm
        have hprefix := hT k ω' ω (fun i hi => (hag i (Nat.lt_trans hi hkM)).symm)
        change (T ω' ≤ (k : WithTop ℕ)) ↔ (T ω ≤ (k : WithTop ℕ)) at hprefix
        have hleft : T ω' ≤ (k : WithTop ℕ) := by
          apply (min_coe_le_iff hkM (T ω')).mp
          simpa [hz]
        have hright : ¬ T ω ≤ (k : WithTop ℕ) := by
          intro htk
          have hmin : min (T ω) (M : WithTop ℕ) ≤ (k : WithTop ℕ) :=
            (min_coe_le_iff hkM (T ω)).mpr htk
          exact (not_le_of_gt (by simpa [hz] using hlt)) hmin
        exact hright (hprefix.mp hleft)
  have hge : min (T ω') (M : WithTop ℕ) ≤ min (T ω) (M : WithTop ℕ) := by
    by_contra hnot
    have hlt : min (T ω) (M : WithTop ℕ) < min (T ω') (M : WithTop ℕ) := lt_of_not_ge hnot
    have hboundLeft : min (T ω) (M : WithTop ℕ) ≤ (M : WithTop ℕ) := min_le_right _ _
    have hboundRight : min (T ω') (M : WithTop ℕ) ≤ (M : WithTop ℕ) := min_le_right _ _
    cases hz : min (T ω) (M : WithTop ℕ) with
    | top =>
        have htop : (⊤ : WithTop ℕ) ≤ (M : WithTop ℕ) := by
          rw [← hz]
          exact hboundLeft
        exact (by simpa using htop)
    | coe k =>
        have hkM : k < M := by
          have hkm : (k : WithTop ℕ) < (M : WithTop ℕ) := by
            simpa [hz] using lt_of_lt_of_le hlt hboundRight
          exact WithTop.coe_lt_coe.mp hkm
        have hprefix := hT k ω ω' (fun i hi => hag i (Nat.lt_trans hi hkM))
        change (T ω ≤ (k : WithTop ℕ)) ↔ (T ω' ≤ (k : WithTop ℕ)) at hprefix
        have hleft : T ω ≤ (k : WithTop ℕ) := by
          apply (min_coe_le_iff hkM (T ω)).mp
          simpa [hz]
        have hright : ¬ T ω' ≤ (k : WithTop ℕ) := by
          intro htk
          have hmin : min (T ω') (M : WithTop ℕ) ≤ (k : WithTop ℕ) :=
            (min_coe_le_iff hkM (T ω')).mpr htk
          exact (not_le_of_gt (by simpa [hz] using hlt)) hmin
        exact hright (hprefix.mp hleft)
  exact le_antisymm hle hge

private lemma pair_nonempty_of_card_ge_two {V : Type*} [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  have hpos : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hpos
  let a : V := Classical.choice (inferInstance : Nonempty V)
  have hone : 1 < Fintype.card V := by omega
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card hone a
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hv
  rcases Sym2.eq_iff.mp hv with ⟨hav, hbv⟩ | ⟨hbv, hav⟩
  · exact hba (hbv.trans hav.symm)
  · exact hba (hav.trans hbv.symm)

/-- Paper `def:pre-process`; blueprint P1-04d. -/
theorem S3_04dStatement_holds : ThLean.BP.S3.S3_04dStatement := by
  classical
  intro V inst hV
  constructor
  · intro a j m
    change PrefixEvent m (fun ω => degreeHittingTime a j ω ≤ (m : WithTop ℕ))
    intro ω ω' hag
    change (degreeHittingTime a j ω ≤ (m : WithTop ℕ)) ↔
      (degreeHittingTime a j ω' ≤ (m : WithTop ℕ))
    have htuple : (fun i : Fin m => ω i.val) = (fun i : Fin m => ω' i.val) := by
      funext i
      exact hag i.val i.isLt
    have hgraph : processGraph ω m = processGraph ω' m := by
      unfold processGraph
      rw [htuple]
    have htime (ξ : EdgeStream V) :
        degreeHittingTime a j ξ ≤ (m : WithTop ℕ) ↔
          j ≤ degree (processGraph ξ m) a := by
      have hmono : ∀ k l, k ≤ l → j ≤ degree (processGraph ξ k) a →
          j ≤ degree (processGraph ξ l) a := by
        intro k l hkl hk
        exact le_trans hk (degree_process_mono ξ hkl a)
      simpa [degreeHittingTime] using
        (firstFailure_le_iff (P := fun k => j ≤ degree (processGraph ξ k) a) hmono m)
    rw [htime ω, htime ω', hgraph]
  · intro T hT M
    let p : Pair V := Classical.choice (pair_nonempty_of_card_ge_two hV)
    let t : EdgeTuple V M → WithTop ℕ :=
      fun x => min (T (finiteExtension p x)) (M : WithTop ℕ)
    have ht : IsFiniteStoppingTime t := by
      intro m x y hxy
      by_cases hm : m < M
      · have hag : AgreeUpTo m (finiteExtension p x) (finiteExtension p y) := by
          intro i hi
          have hiM : i < M := Nat.lt_trans hi hm
          simp only [finiteExtension, hiM]
          exact hxy ⟨i, hiM⟩ hi
        have hprefix := hT m (finiteExtension p x) (finiteExtension p y) hag
        change (T (finiteExtension p x) ≤ (m : WithTop ℕ)) ↔
          (T (finiteExtension p y) ≤ (m : WithTop ℕ)) at hprefix
        change (min (T (finiteExtension p x)) (M : WithTop ℕ) ≤ (m : WithTop ℕ)) ↔
          (min (T (finiteExtension p y)) (M : WithTop ℕ) ≤ (m : WithTop ℕ))
        rw [min_coe_le_iff hm, min_coe_le_iff hm]
        exact hprefix
      · have hmM : M ≤ m := Nat.le_of_not_gt hm
        have hx : min (T (finiteExtension p x)) (M : WithTop ℕ) ≤ (m : WithTop ℕ) :=
          le_trans (min_le_right _ _) (WithTop.coe_le_coe.mpr hmM)
        have hy : min (T (finiteExtension p y)) (M : WithTop ℕ) ≤ (m : WithTop ℕ) :=
          le_trans (min_le_right _ _) (WithTop.coe_le_coe.mpr hmM)
        exact iff_of_true hx hy
    have hspec : ∀ ω : EdgeStream V,
        t (fun i : Fin M => ω i.val) = min (T ω) (M : WithTop ℕ) := by
      intro ω
      let x : EdgeTuple V M := fun i => ω i.val
      have hag : AgreeUpTo M (finiteExtension p x) ω := by
        intro i hi
        simp [finiteExtension, x, hi]
      have hcap := min_stopping_invariant T hT hag
      simpa [t, finiteExtension, x] using hcap
    refine ⟨t, ⟨ht, hspec⟩, ?_⟩
    intro s hs
    funext x
    have hspec' := hs.2 (finiteExtension p x)
    have htuple : (fun i : Fin M => finiteExtension p x i.val) = x := by
      funext i
      simp [finiteExtension, i.isLt]
    rw [htuple] at hspec'
    change s x = min (T (finiteExtension p x)) (M : WithTop ℕ) at hspec'
    change s x = t x
    simpa [t] using hspec'

end ThLean.W.S394

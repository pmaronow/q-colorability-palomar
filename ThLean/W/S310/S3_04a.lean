import ThLean.BP.S3.Process

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S310

open ThresholdFoundations
open ThLean.BP.S3

private theorem colorable_of_subgraph {V : Type*} (q : ℕ) (G H : MGraph V)
    (hGH : subgraph G H) (hH : Colorable q H) : Colorable q G := by
  rcases hH with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro u v huv
  exact hσ u v (lt_of_lt_of_le huv (hGH (s(u,v))))

private theorem tupleGraph_prefix_subgraph {V : Type*} [Fintype V]
    {m n : ℕ} (ι : Fin m ↪ Fin n) (x : Fin n → Pair V) :
    subgraph (tupleGraph (fun j : Fin m => x (ι j))) (tupleGraph x) := by
  classical
  intro e
  change (Finset.univ.filter (fun j : Fin m => (x (ι j)).val = e)).card ≤
    (Finset.univ.filter (fun j : Fin n => (x j).val = e)).card
  apply Finset.card_le_card_of_injOn ι
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨_, hje⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hje⟩
  · intro i hi j hj hij
    exact ι.injective hij

private theorem processGraph_agree {V : Type*} [Fintype V]
    (ω ω' : EdgeStream V) (m k : ℕ) (hkm : k ≤ m)
    (hag : ∀ i, i < m → ω i = ω' i) :
    processGraph ω k = processGraph ω' k := by
  classical
  funext e
  change (Finset.univ.filter (fun i : Fin k => (ω i.val).val = e)).card =
    (Finset.univ.filter (fun i : Fin k => (ω' i.val).val = e)).card
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [hag i.val (by omega)]

private theorem processGraph_prefix_subgraph {V : Type*} [Fintype V]
    (ω : EdgeStream V) {k m : ℕ} (hkm : k ≤ m) :
    subgraph (processGraph ω k) (processGraph ω m) := by
  let ι : Fin k ↪ Fin m :=
    ⟨fun j => ⟨j.val, lt_of_lt_of_le j.isLt hkm⟩,
      fun i j hij => Fin.ext (congrArg (fun z : Fin m => z.val) hij)⟩
  change subgraph (tupleGraph (fun j : Fin k => ω (ι j).val))
    (tupleGraph (fun i : Fin m => ω i.val))
  exact tupleGraph_prefix_subgraph ι (fun i : Fin m => ω i.val)

private theorem firstFailure_le_iff (P : ℕ → Prop) (m : ℕ) :
    firstFailure P ≤ (m : WithTop ℕ) ↔ ∃ k ≤ m, P k := by
  classical
  unfold firstFailure
  by_cases hex : ∃ k, P k
  · simp only [dif_pos hex]
    constructor
    · intro hle
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
      exact WithTop.coe_le_coe.mp hle
    · rintro ⟨k, hkm, hk⟩
      exact WithTop.coe_le_coe.mpr (le_trans (Nat.find_min' hex hk) hkm)
  · simp only [dif_neg hex]
    constructor
    · intro h
      exact False.elim (by simpa using h)
    · rintro ⟨k, hkm, hk⟩
      exact False.elim (hex ⟨k, hk⟩)

private theorem hittingTime_le_iff {V : Type*} [Fintype V]
    (q : ℕ) (ω : EdgeStream V) (m : ℕ) :
    hittingTime q ω ≤ (m : WithTop ℕ) ↔
      ∃ k ≤ m, ¬ Colorable q (processGraph ω k) := by
  exact firstFailure_le_iff _ _

private theorem hittingTime_colorable_iff {V : Type*} [Fintype V]
    (q : ℕ) (ω : EdgeStream V) (m : ℕ) :
    ((m : WithTop ℕ) < hittingTime q ω ↔ Colorable q (processGraph ω m)) := by
  constructor
  · intro hlt
    by_contra hcol
    have hle := (hittingTime_le_iff q ω m).2 ⟨m, le_rfl, hcol⟩
    exact (not_le_of_gt hlt) hle
  · intro hcol
    apply lt_of_not_ge
    intro hle
    obtain ⟨k, hkm, hbad⟩ := (hittingTime_le_iff q ω m).mp hle
    have hprefix : subgraph (processGraph ω k) (processGraph ω m) := by
      exact processGraph_prefix_subgraph ω hkm
    exact hbad (colorable_of_subgraph q _ _ hprefix hcol)

private theorem succ_eq_of_lt_le {m : ℕ} {T : WithTop ℕ}
    (hlt : (m : WithTop ℕ) < T) (hle : T ≤ ((m+1 : ℕ) : WithTop ℕ)) :
    T = ((m+1 : ℕ) : WithTop ℕ) := by
  cases T with
  | top => simp at hle
  | coe t =>
    have hlt' : m < t := WithTop.coe_lt_coe.mp hlt
    have hle' : t ≤ m+1 := WithTop.coe_le_coe.mp hle
    have ht : t = m+1 := by omega
    exact congrArg (fun k : ℕ => (k : WithTop ℕ)) ht

private theorem processSurvival_zero_time {V : Type*} [Fintype V] (q : ℕ) (hq : 0 < q) :
    processSurvival (V := V) q 0 = 1 := by
  have hg (x : EdgeTuple V 0) : tupleGraph x = 0 := by
    ext e
    simp [tupleGraph]
  have hc (x : EdgeTuple V 0) : Colorable q (tupleGraph x) := by
    refine ⟨fun _ => ⟨0, hq⟩, ?_⟩
    intro u v huv
    rw [hg x] at huv
    simp at huv
  simp [processSurvival, survival, uniformProb, uniformMean, indicator, hc]

private theorem processSurvival_zero_of_empty_pairs {V : Type*} [Fintype V]
    (q m : ℕ) (hm : 0 < m) (hpair : ¬ Nonempty (Pair V)) :
    processSurvival (V := V) q m = 0 := by
  classical
  letI : IsEmpty (Pair V) := ⟨fun e => hpair ⟨e⟩⟩
  letI : IsEmpty (EdgeTuple V m) := ⟨fun x => hpair ⟨x ⟨0, hm⟩⟩⟩
  simp [processSurvival, survival, uniformProb, uniformMean]

private theorem processSurvival_antitone_of_nonempty_pairs {V : Type u} [Fintype V]
    (hproj : S3_02Statement.{u}) (q : ℕ) (m n : ℕ) (hmn : m ≤ n)
    (hpair : Nonempty (Pair V)) :
    processSurvival (V := V) q n ≤ processSurvival (V := V) q m := by
  classical
  letI : Nonempty (Pair V) := hpair
  let ι : Fin m ↪ Fin n :=
    ⟨fun j => ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩,
      fun i j hij => Fin.ext (congrArg (fun z : Fin n => z.val) hij)⟩
  let F : EdgeTuple V m → ℝ := fun x => indicator (Colorable q (tupleGraph x))
  have hproject := (hproj (Pair V) n m ι).2.2.1 F
  have hpoint : ∀ x : EdgeTuple V n,
      indicator (Colorable q (tupleGraph x)) ≤
        indicator (Colorable q (tupleGraph (fun j : Fin m => x (ι j)))) := by
    intro x
    have hsub := tupleGraph_prefix_subgraph ι x
    by_cases hc : Colorable q (tupleGraph x)
    · have hpref : Colorable q (tupleGraph (fun j : Fin m => x (ι j))) :=
        colorable_of_subgraph q _ _ hsub hc
      simp [indicator, hc, hpref]
    · by_cases hpref : Colorable q (tupleGraph (fun j : Fin m => x (ι j)))
      · simp [indicator, hc, hpref]
      · simp [indicator, hc, hpref]
  have hmean_le :
      uniformMean (fun x : EdgeTuple V n => indicator (Colorable q (tupleGraph x))) ≤
        uniformMean (fun x : EdgeTuple V n =>
          indicator (Colorable q (tupleGraph (fun j : Fin m => x (ι j))))) := by
    unfold uniformMean
    have hc : 0 < (Fintype.card (EdgeTuple V n) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (show Nonempty (EdgeTuple V n) from inferInstance))
    rw [div_le_div_iff_of_pos_right hc]
    exact Finset.sum_le_sum (fun x hx => hpoint x)
  have hmean_eq :
      uniformMean (fun x : EdgeTuple V n =>
          indicator (Colorable q (tupleGraph (fun j : Fin m => x (ι j))))) =
        uniformMean (fun x : EdgeTuple V m => indicator (Colorable q (tupleGraph x))) := by
    exact hproject
  unfold processSurvival survival uniformProb
  simp only [zero_add]
  exact hmean_le.trans_eq hmean_eq

theorem S3_04aStatement_of_deps
    (hproj : ThLean.BP.S3.S3_02Statement.{u}) :
    ThLean.BP.S3.S3_04aStatement.{u} := by
  intro V _ q hq
  have hfirst : ∀ ω : EdgeStream V, (1 : WithTop ℕ) ≤ hittingTime q ω := by
    intro ω
    have hzero : Colorable q (processGraph ω 0) := by
      have hg : processGraph ω 0 = 0 := by
        ext e
        simp [processGraph, tupleGraph]
      rw [hg]
      refine ⟨fun _ => ⟨0, by omega⟩, ?_⟩
      intro a b hab
      simp at hab
    have hnot : ¬ hittingTime q ω ≤ (0 : WithTop ℕ) := by
      intro hle
      obtain ⟨k, hkm, hk⟩ := (hittingTime_le_iff q ω 0).mp hle
      have : k = 0 := by omega
      subst k
      exact hk hzero
    cases ht : hittingTime q ω with
    | top => simp [ht]
    | coe t =>
      have htnz : t ≠ 0 := by
        intro ht0
        apply hnot
        rw [ht, ht0]
        exact le_rfl
      exact WithTop.coe_le_coe.mpr (Nat.one_le_iff_ne_zero.mpr htnz)
  have htime : ∀ (ω : EdgeStream V) (m : ℕ),
      ((m : WithTop ℕ) < hittingTime q ω ↔ Colorable q (processGraph ω m)) ∧
      (hittingTime q ω = ((m+1 : ℕ) : WithTop ℕ) ↔
        Colorable q (processGraph ω m) ∧ ¬ Colorable q (processGraph ω (m+1))) := by
    intro ω m
    refine ⟨hittingTime_colorable_iff q ω m, ?_⟩
    constructor
    · intro hEq
      have hcol := (hittingTime_colorable_iff q ω m).mp (by rw [hEq]; exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self m))
      have hle : hittingTime q ω ≤ ((m+1 : ℕ) : WithTop ℕ) := by rw [hEq]
      obtain ⟨k, hkm, hbad⟩ := (hittingTime_le_iff q ω (m+1)).mp hle
      have hnotle : ¬ k ≤ m := by
        intro hkm'
        have hprefix : subgraph (processGraph ω k) (processGraph ω m) := by
          exact processGraph_prefix_subgraph ω hkm'
        exact hbad (colorable_of_subgraph q _ _ hprefix hcol)
      have hk : k = m+1 := by omega
      subst k
      exact ⟨hcol, hbad⟩
    · rintro ⟨hcol, hbad⟩
      have hlt : (m : WithTop ℕ) < hittingTime q ω :=
        (hittingTime_colorable_iff q ω m).mpr hcol
      have hle : hittingTime q ω ≤ ((m+1 : ℕ) : WithTop ℕ) :=
        (hittingTime_le_iff q ω (m+1)).2 ⟨m+1, le_rfl, hbad⟩
      exact succ_eq_of_lt_le hlt hle
  have hstop : IsStoppingTime (hittingTime (V := V) q) := by
    intro m ω ω' hag
    constructor
    · intro hle
      obtain ⟨k, hkm, hk⟩ := (hittingTime_le_iff q ω m).mp hle
      apply (hittingTime_le_iff q ω' m).2
      refine ⟨k, hkm, ?_⟩
      have heq := processGraph_agree ω ω' m k hkm hag
      rw [← heq]
      exact hk
    · intro hle
      obtain ⟨k, hkm, hk⟩ := (hittingTime_le_iff q ω' m).mp hle
      apply (hittingTime_le_iff q ω m).2
      refine ⟨k, hkm, ?_⟩
      have heq := processGraph_agree ω ω' m k hkm hag
      rw [heq]
      exact hk
  have hsurv : Antitone (processSurvival (V := V) q) := by
    intro m n hmn
    by_cases hpair : Nonempty (Pair V)
    · exact processSurvival_antitone_of_nonempty_pairs hproj q m n hmn hpair
    · by_cases hm : m = 0
      · subst m
        by_cases hn : n = 0
        · subst n
          exact le_rfl
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          rw [processSurvival_zero_time q (by omega), processSurvival_zero_of_empty_pairs q n hnpos hpair]
          norm_num
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hnpos : 0 < n := lt_of_lt_of_le hmpos hmn
        rw [processSurvival_zero_of_empty_pairs q n hnpos hpair,
          processSurvival_zero_of_empty_pairs q m hmpos hpair]
  exact ⟨hfirst, ⟨htime, hstop, hsurv⟩⟩

end ThLean.W.S310

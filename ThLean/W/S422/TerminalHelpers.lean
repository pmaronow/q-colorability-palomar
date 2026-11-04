module

public import ThLean.BP.S4.Deletion

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ThLean.W.S422
open ThresholdFoundations ThLean.BP.S4

lemma uniformMean_snoc_init {E : Type} [Fintype E] [Nonempty E]
    (m : ℕ) (f : (Fin m → E) → ℝ) :
    uniformMean (fun x : Fin (m+1) → E => f (fun i => x i.castSucc)) =
      uniformMean f := by
  classical
  unfold uniformMean
  let e := Fin.snocEquiv (fun _ : Fin (m+1) => E)
  have hsum :
      (∑ x : Fin (m+1) → E, f (fun i => x i.castSucc)) =
        (Fintype.card E : ℝ) * ∑ y : Fin m → E, f y := by
    calc
      (∑ x : Fin (m+1) → E, f (fun i => x i.castSucc)) =
          ∑ p : E × (Fin m → E), f p.2 := by
            symm
            apply Fintype.sum_equiv e
            intro p
            simp [e, Fin.snocEquiv]
      _ = (Fintype.card E : ℝ) * ∑ y : Fin m → E, f y := by
            simp [Fintype.sum_prod_type]
  have hcard : Fintype.card (Fin (m+1) → E) =
      Fintype.card E * Fintype.card (Fin m → E) := by
    calc
      Fintype.card (Fin (m+1) → E) = Fintype.card (E × (Fin m → E)) :=
        Fintype.card_congr e.symm
      _ = Fintype.card E * Fintype.card (Fin m → E) := by simp
  rw [hsum, hcard]
  push_cast
  have hc : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := E))
  field_simp [hc]

lemma uniformMean_prefix {E : Type} [Fintype E] [Nonempty E]
    (r s : ℕ) (f : (Fin r → E) → ℝ) :
    uniformMean (fun x : Fin (r+s) → E =>
      f (fun i => x ⟨i.val, by omega⟩)) = uniformMean f := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      change uniformMean (fun x : Fin ((r+s)+1) → E =>
        f (fun i => x ⟨i.val, by omega⟩)) = _
      calc
        uniformMean (fun x : Fin ((r+s)+1) → E =>
            f (fun i => x ⟨i.val, by omega⟩)) =
          uniformMean (fun y : Fin (r+s) → E =>
            f (fun i => y ⟨i.val, by omega⟩)) := by
              simpa using uniformMean_snoc_init (m := r+s)
                (f := fun y : Fin (r+s) → E => f (fun i => y ⟨i.val, by omega⟩))
        _ = uniformMean f := ih

lemma tuplePrefix_eq_tupleGraph_restrict {V : Type} [Fintype V]
    {T k : ℕ} (x : EdgeTuple V T) (h : k ≤ T) :
    tuplePrefix x k = tupleGraph (restrictTuple h x) := by
  classical
  funext e
  change (Finset.univ.filter (fun i : Fin T => i.val < k ∧ (x i).val = e)).card =
    (Finset.univ.filter (fun i : Fin k =>
      (x ⟨i.val, by omega⟩).val = e)).card
  apply Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2.1⟩)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using (Finset.mem_filter.mp hi).2.2
  · intro i hi j hj hij
    apply Fin.ext
    simpa using congrArg (fun z : Fin k => z.val) hij
  · intro j hj
    refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by omega, ?_⟩
      simpa using (Finset.mem_filter.mp hj).2
    · apply Fin.ext
      rfl

lemma tupleGraph_apply_count {V : Type} [Fintype V] {m : ℕ}
    (y : EdgeTuple V m) (e : Sym2 V) :
    tupleGraph y e = ∑ i : Fin m, if (y i).val = e then 1 else 0 := by
  classical
  unfold tupleGraph
  rw [Finset.card_filter]

lemma tupleGraph_snoc {V : Type} [Fintype V] {m : ℕ}
    (y : EdgeTuple V m) (e : Pair V) :
    tupleGraph (Fin.snoc (α := fun _ : Fin (m+1) => Pair V) y e) =
      addPair (tupleGraph y) e := by
  classical
  funext f
  rw [tupleGraph_apply_count (Fin.snoc (α := fun _ : Fin (m+1) => Pair V) y e) f]
  change (∑ i : Fin (m+1),
      if (Fin.snoc (α := fun _ : Fin (m+1) => Pair V) y e i).val = f then 1 else 0) =
    Function.update (tupleGraph y) e.val (tupleGraph y e.val + 1) f
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change (∑ i : Fin m, if (y i).val = f then 1 else 0) +
      (if e.val = f then 1 else 0) =
    Function.update (tupleGraph y) e.val (tupleGraph y e.val + 1) f
  by_cases hf : e.val = f
  · subst f
    rw [tupleGraph_apply_count y e.val]
    simp
  · have hsum := tupleGraph_apply_count y f
    have hne : f ≠ e.val := Ne.symm hf
    rw [if_neg hf, ← hsum]
    simp [Function.update, hne]

lemma tuplePrefix_snoc {V : Type} [Fintype V] {m : ℕ}
    (z : EdgeTuple V (m+1)) :
    tuplePrefix z m = tupleGraph (fun i => z i.castSucc) ∧
      tuplePrefix z (m+1) =
        addPair (tupleGraph (fun i => z i.castSucc)) (z (Fin.last m)) := by
  classical
  let y : EdgeTuple V m := fun i => z i.castSucc
  have hy : restrictTuple (by omega : m ≤ m+1) z = y := by
    funext i
    apply congrArg z
    apply Fin.ext
    rfl
  have hfull : restrictTuple (by omega : m+1 ≤ m+1) z = z := by
    funext i
    simp [restrictTuple]
  have hz : z = Fin.snoc (α := fun _ : Fin (m+1) => Pair V) y (z (Fin.last m)) := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [y, Fin.snoc_castSucc]
    · simp [Fin.snoc_last]
  constructor
  · rw [tuplePrefix_eq_tupleGraph_restrict z (by omega), hy]
  · calc
      tuplePrefix z (m+1) = tupleGraph (restrictTuple (by omega : m+1 ≤ m+1) z) :=
        tuplePrefix_eq_tupleGraph_restrict z (by omega)
      _ = tupleGraph z := by rw [hfull]
      _ = tupleGraph (Fin.snoc (α := fun _ : Fin (m+1) => Pair V) y (z (Fin.last m))) := by
        exact congrArg tupleGraph hz
      _ = addPair (tupleGraph y) (z (Fin.last m)) := tupleGraph_snoc y _

lemma tuplePrefix_restrict_consistency {V : Type} [Fintype V]
    {T r m : ℕ} (x : EdgeTuple V T) (hr : r ≤ T) (hm : m ≤ r) :
    tuplePrefix x m = tuplePrefix (restrictTuple hr x) m := by
  rw [tuplePrefix_eq_tupleGraph_restrict x (le_trans hm hr)]
  rw [tuplePrefix_eq_tupleGraph_restrict (restrictTuple hr x) hm]
  congr 1

lemma pair_nonempty_fin {n : ℕ} (hn : 2 ≤ n) :
    Nonempty (Pair (Fin n)) := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    simp [a, b] at hv
  refine ⟨⟨s(a,b), ?_⟩⟩
  intro v hv
  rcases Sym2.eq_iff.mp hv with h | h
  · exact hab (h.1.trans h.2.symm)
  · exact hab (h.1.trans h.2.symm)

lemma tuplePrefix_subgraph {V : Type} [Fintype V] {T : ℕ}
    (x : EdgeTuple V T) {m m' : ℕ} (h : m ≤ m') :
    subgraph (tuplePrefix x m) (tuplePrefix x m') := by
  classical
  intro e
  unfold tuplePrefix
  apply Finset.card_mono
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨by omega, hi.2⟩

lemma colorable_of_subgraph {V : Type} [Fintype V] {q : ℕ}
    {G G' : MGraph V} (hsub : subgraph G G') (hc : Colorable q G') :
    Colorable q G := by
  rcases hc with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro u v huv
  apply hσ u v
  exact lt_of_lt_of_le huv (hsub (s(u,v)))

lemma colorable_zero_graph {V : Type} (q : ℕ) (hq : 0 < q) :
    Colorable q (0 : MGraph V) := by
  refine ⟨fun _ => ⟨0, hq⟩, ?_⟩
  intro u v huv
  simp at huv

lemma tuplePrefix_zero {V : Type} [Fintype V] {T : ℕ}
    (x : EdgeTuple V T) : tuplePrefix x 0 = 0 := by
  classical
  funext e
  simp [tuplePrefix]

lemma transition_count {V : Type} [Fintype V] {T q k : ℕ}
    (x : EdgeTuple V T) (hk : k < T)
    (ht : Colorable q (tuplePrefix x k) ∧
      ¬ Colorable q (tuplePrefix x (k+1))) :
    cappedLast q x = k := by
  classical
  let f : ℕ → ℕ := fun i =>
    if Colorable q (tuplePrefix x (i+1)) then 1 else 0
  have hsplit := Finset.sum_range_add_sum_Ico f (Nat.le_of_lt hk)
  unfold cappedLast
  rw [← hsplit]
  have hfirst : (∑ i ∈ Finset.range k, f i) = k := by
    calc
      (∑ i ∈ Finset.range k, f i) = ∑ i ∈ Finset.range k, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < k := Finset.mem_range.mp hi
        have hcolor : Colorable q (tuplePrefix x (i+1)) :=
          colorable_of_subgraph (tuplePrefix_subgraph x (by omega)) ht.1
        simp [f, hcolor]
      _ = k := by simp
  have htail : (∑ i ∈ Finset.Ico k T, f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hnot : ¬ Colorable q (tuplePrefix x (i+1)) := by
      intro hc
      apply ht.2
      exact colorable_of_subgraph (tuplePrefix_subgraph x (by omega)) hc
    simp [f, hnot]
  omega

lemma cap_transition {V : Type} [Fintype V] {T q k : ℕ}
    (x : EdgeTuple V T) (hq : 0 < q) (hk : k < T)
    (hc : cappedLast q x = k) :
    Colorable q (tuplePrefix x k) ∧
      ¬ Colorable q (tuplePrefix x (k+1)) := by
  classical
  constructor
  · by_contra hbad
    by_cases hk0 : k = 0
    · have hempty : Colorable q (tuplePrefix x k) := by
        rw [hk0, tuplePrefix_zero]
        exact colorable_zero_graph (V := V) q hq
      exact hbad hempty
    · have hsplit := Finset.sum_range_add_sum_Ico
        (fun i => if Colorable q (tuplePrefix x (i+1)) then 1 else 0)
        (m := k-1) (n := T) (by omega)
      have hsmall :
          (∑ i ∈ Finset.range (k-1),
            if Colorable q (tuplePrefix x (i+1)) then 1 else 0) ≤ k-1 := by
        calc
          _ ≤ ∑ i ∈ Finset.range (k-1), (1 : ℕ) := by
            apply Finset.sum_le_sum
            intro i hi
            split_ifs <;> omega
          _ = k-1 := by simp
      have hzero :
          (∑ i ∈ Finset.Ico (k-1) T,
            if Colorable q (tuplePrefix x (i+1)) then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        have hnot : ¬ Colorable q (tuplePrefix x (i+1)) := by
          intro hc'
          exact hbad (colorable_of_subgraph
            (tuplePrefix_subgraph x (by omega)) hc')
        simp [hnot]
      unfold cappedLast at hc
      rw [← hsplit] at hc
      omega
  · by_contra hbad
    have hbig : k+1 ≤ cappedLast q x := by
      have hsplit := Finset.sum_range_add_sum_Ico
        (fun i => if Colorable q (tuplePrefix x (i+1)) then 1 else 0)
        (m := k+1) (n := T) (by omega)
      have hfirst :
          (∑ i ∈ Finset.range (k+1),
            if Colorable q (tuplePrefix x (i+1)) then 1 else 0) = k+1 := by
        calc
          (∑ i ∈ Finset.range (k+1),
              if Colorable q (tuplePrefix x (i+1)) then 1 else 0) =
              ∑ i ∈ Finset.range (k+1), (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hi' : i < k+1 := Finset.mem_range.mp hi
            have hcolor : Colorable q (tuplePrefix x (i+1)) :=
              colorable_of_subgraph (tuplePrefix_subgraph x (by omega)) hbad
            simp [hcolor]
          _ = k+1 := by simp
      have htail :
          0 ≤ (∑ i ∈ Finset.Ico (k+1) T,
            if Colorable q (tuplePrefix x (i+1)) then 1 else 0) := Nat.zero_le _
      unfold cappedLast
      rw [← hsplit]
      omega
    omega

lemma empty_prefix_colorable {V : Type} [Fintype V] {T q : ℕ}
    (x : EdgeTuple V T) (hq : 0 < q) : Colorable q (tuplePrefix x 0) := by
  rw [tuplePrefix_zero]
  exact colorable_zero_graph q hq

lemma uniformMean_equiv {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) (f : B → ℝ) :
    uniformMean (fun a => f (e a)) = uniformMean f := by
  classical
  unfold uniformMean
  have hs := Fintype.sum_equiv e (fun a => f (e a)) f (fun _ => rfl)
  have hc := Fintype.card_congr e
  rw [hs, hc]

lemma uniformMean_fintype_indep {A : Type} (i₁ i₂ : Fintype A) (f : A → ℝ) :
    @uniformMean A i₁ f = @uniformMean A i₂ f := by
  classical
  have hs : (@Finset.univ A i₁) = (@Finset.univ A i₂) := by
    ext a
    simp
  have hc : @Fintype.card A i₁ = @Fintype.card A i₂ := by
    change (@Finset.univ A i₁).card = (@Finset.univ A i₂).card
    rw [hs]
  unfold uniformMean
  rw [hs, hc]

lemma uniformMean_prod {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  classical
  unfold uniformMean
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  push_cast
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := A)
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := B)
  field_simp [hA, hB]
  simp_rw [div_eq_mul_inv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  field_simp [hB]

lemma uniformMean_snoc_prod {E : Type} [Fintype E] [Nonempty E]
    (m : ℕ) (f : (Fin m → E) → E → ℝ) :
    uniformMean (fun z : Fin (m+1) → E =>
      f (fun i => z i.castSucc) (z (Fin.last m))) =
    uniformMean (fun y : Fin m → E => uniformMean (fun e => f y e)) := by
  classical
  let e : (Fin m → E) × E ≃ (Fin (m+1) → E) :=
    (Equiv.prodComm (Fin m → E) E).trans
      (Fin.snocEquiv (fun _ : Fin (m+1) => E))
  calc
    uniformMean (fun z : Fin (m+1) → E =>
        f (fun i => z i.castSucc) (z (Fin.last m))) =
      uniformMean (fun p : (Fin m → E) × E => f p.1 p.2) := by
        symm
        simpa [e, Fin.snocEquiv] using
          (uniformMean_equiv e (fun z : Fin (m+1) → E =>
            f (fun i => z i.castSucc) (z (Fin.last m))) )
    _ = uniformMean (fun y : Fin m → E => uniformMean (fun a => f y a)) :=
      uniformMean_prod (fun p : (Fin m → E) × E => f p.1 p.2)

end ThLean.W.S422

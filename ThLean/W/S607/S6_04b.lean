module

public import ThLean.BP.S6.Foundation

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S607

private theorem occurrence_filter_card
    {V : Type*} [Fintype V] (G : MGraph V) (P : Sym2 V → Prop) :
    (Finset.univ.filter (fun o : Occurrence G => P o.1)).card =
      ∑ e : Sym2 V, if P e then G e else 0 := by
  classical
  let A := {o : Occurrence G // P o.1}
  let B := Σ e : Sym2 V, {i : Fin (G e) // P e}
  let equivAB : A ≃ B :=
    { toFun := fun o => ⟨o.1.1, ⟨o.1.2, o.2⟩⟩
      invFun := fun o => ⟨⟨o.1, o.2.1⟩, o.2.2⟩
      left_inv := by intro o; cases o; rfl
      right_inv := by intro o; cases o; rfl }
  have hcard : Fintype.card A = Fintype.card B := Fintype.card_congr equivAB
  have hsub : (Finset.univ.filter (fun o : Occurrence G => P o.1)).card =
      Fintype.card A := by
    exact (Fintype.card_of_subtype
      (Finset.univ.filter (fun o : Occurrence G => P o.1))
      (by intro o; simp [A])).symm
  rw [hsub, hcard, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hp : P e
  · simp [hp]
  · simp [hp]

private theorem eraseEdge_positive_imp
    {V : Type*} [Fintype V] (G : MGraph V) (e : Sym2 V) (hpos : 0 < G e)
    (x : Sym2 V) : 0 < eraseEdge G e x → 0 < G x := by
  classical
  by_cases hx : x = e
  · subst x
    simp [eraseEdge, hpos]
  · simpa [eraseEdge, hx]

private theorem eraseEdge_positive_iff_of_two
    {V : Type*} [Fintype V] (G : MGraph V) (e : Sym2 V) (hge : 2 ≤ G e)
    (x : Sym2 V) : 0 < eraseEdge G e x ↔ 0 < G x := by
  classical
  by_cases hx : x = e
  · subst x
    simp [eraseEdge, hge]
    omega
  · simp [eraseEdge, hx]

private theorem eraseEdge_coloring_iff
    {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V) (e : Sym2 V)
    (hpos : ∀ x, 0 < eraseEdge G e x ↔ 0 < G x) (σ : V → Fin q) :
    IsColoring q (eraseEdge G e) σ ↔ IsColoring q G σ := by
  constructor
  · intro h a b hab
    exact h a b ((hpos (s(a, b))).2 hab)
  · intro h a b hab
    exact h a b ((hpos (s(a, b))).1 hab)

private theorem eraseEdge_frozen_of_two
    {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V) (e : Sym2 V)
    (u v : V) (hge : 2 ≤ G e) (hFrozen : Frozen q G u v) :
    Frozen q (eraseEdge G e) u v := by
  rcases hFrozen with ⟨hColorable, hSame⟩
  refine ⟨?_, ?_⟩
  · rcases hColorable with ⟨σ, hσ⟩
    exact ⟨σ, (eraseEdge_coloring_iff q G e
      (fun x => eraseEdge_positive_iff_of_two G e hge x) σ).2 hσ⟩
  · intro σ hσ
    apply hSame σ
    exact (eraseEdge_coloring_iff q G e
      (fun x => eraseEdge_positive_iff_of_two G e hge x) σ).1 hσ

private theorem eraseEdge_colorable_of_pos
    {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V) (e : Sym2 V)
    (hpos : 0 < G e) (hColorable : Colorable q G) :
    Colorable q (eraseEdge G e) := by
  rcases hColorable with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro a b hab
  exact hσ a b (eraseEdge_positive_imp G e hpos (s(a, b)) hab)

private theorem degree_eraseEdge_add_one
    {V : Type*} [Fintype V] (G : MGraph V) (u : V) (e : Sym2 V)
    (hpos : 0 < G e) (htouch : Touches u e) :
    degree (eraseEdge G e) u + 1 = degree G u := by
  classical
  let f : Sym2 V → ℕ := fun x => if Touches u x then G x else 0
  let f' : Sym2 V → ℕ := fun x => if Touches u x then eraseEdge G e x else 0
  have hmem : e ∈ (Finset.univ : Finset (Sym2 V)) := Finset.mem_univ e
  have hrest : ∑ x ∈ Finset.univ.erase e, f' x = ∑ x ∈ Finset.univ.erase e, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ e := (Finset.mem_erase.mp hx).1
    simp [f, f', eraseEdge, hne]
  have hAt : f' e + 1 = f e := by
    simp [f, f', eraseEdge, htouch]
    omega
  unfold degree
  change (∑ x ∈ Finset.univ, f' x) + 1 = ∑ x ∈ Finset.univ, f x
  rw [← Finset.add_sum_erase Finset.univ f' hmem,
      ← Finset.add_sum_erase Finset.univ f hmem, hrest]
  omega

private theorem occurrence_partition_count
    {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V) (u v : V)
    (hFrozen : Frozen q G u v) :
    degree G u = nonpivotalCount q G u v +
      (Finset.univ.filter (fun o : Occurrence G => Pivotal q G u v o)).card := by
  classical
  let np : Sym2 V → Prop := fun e =>
    Touches u e ∧ Frozen q G u v ∧ Frozen q (eraseEdge G e) u v
  let pv : Sym2 V → Prop := fun e =>
    Touches u e ∧ Frozen q G u v ∧ ¬ Frozen q (eraseEdge G e) u v
  have hnp : nonpivotalCount q G u v = ∑ e, if np e then G e else 0 := by
    simp [nonpivotalCount, np, hFrozen]
  have hpv : (Finset.univ.filter (fun o : Occurrence G => Pivotal q G u v o)).card =
      ∑ e, if pv e then G e else 0 := by
    simpa [Pivotal, pv, hFrozen] using occurrence_filter_card G pv
  have hsplit : ∀ e, (if Touches u e then G e else 0) =
      (if np e then G e else 0) + (if pv e then G e else 0) := by
    intro e
    by_cases ht : Touches u e
    · by_cases he : Frozen q (eraseEdge G e) u v
      · simp [np, pv, hFrozen, ht, he]
      · simp [np, pv, hFrozen, ht, he]
    · simp [np, pv, hFrozen, ht]
  calc
    degree G u = ∑ e, if Touches u e then G e else 0 := rfl
    _ = ∑ e, ((if np e then G e else 0) + (if pv e then G e else 0)) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hsplit e
    _ = (∑ e, if np e then G e else 0) + (∑ e, if pv e then G e else 0) := by
      rw [Finset.sum_add_distrib]
    _ = nonpivotalCount q G u v +
        (Finset.univ.filter (fun o : Occurrence G => Pivotal q G u v o)).card := by
      rw [← hnp, ← hpv]

theorem S6_04bStatement_holds : ThLean.BP.S6.S6_04bStatement := by
  intro n q hn hq
  refine ⟨?_, ?_, ?_⟩
  · intro G u v j K huv hFrozen hdeg hKpos hKj hnp
    have hcount := occurrence_partition_count q G u v hFrozen
    omega
  · intro G u v e hFrozen htouch hmult
    simpa [erasePair] using eraseEdge_frozen_of_two q G e.val u v hmult hFrozen
  · intro G u e hColorable hpos htouch
    refine ⟨?_, ?_⟩
    · simpa [erasePair] using eraseEdge_colorable_of_pos q G e.val hpos hColorable
    · simpa [erasePair] using degree_eraseEdge_add_one G u e.val hpos htouch

end ThLean.W.S607

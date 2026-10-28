import ThLean.BP.S5.Structure

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S561
open ThresholdFoundations
open ThLean.BP.S5

private theorem mapGraph_equiv_apply {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (G : MGraph V) (u v : V) :
    mapGraph e G (s(e u, e v)) = G (s(u, v)) := by
  classical
  unfold mapGraph
  rw [Finset.sum_eq_single (s(u, v))]
  · simp
  · intro x hx hne
    have hnot : Sym2.map e x ≠ s(e u, e v) := by
      intro h
      exact hne ((Sym2.map.injective e.injective) h)
    simp [hnot]
  · simp

private def rootEquiv {V : Type} (a : V) : Option (Outside a) ≃ V where
  toFun := rootMap a
  invFun := by
    classical
    exact fun v => if h : v = a then none else some ⟨v, h⟩
  left_inv := by
    intro x
    cases x with
    | none => simp [rootMap]
    | some x => simp [rootMap, x.property]
  right_inv := by
    intro v
    by_cases h : v = a <;> simp [rootMap, h]

private theorem mapGraph_isColoring_equiv {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (q : ℕ) (G : MGraph V) (τ : W → Fin q) :
    IsColoring q (mapGraph e G) τ ↔ IsColoring q G (τ ∘ e) := by
  constructor
  · intro h u v huv
    apply h (e u) (e v)
    simpa only [mapGraph_equiv_apply] using huv
  · intro h u v huv
    let u' := e.symm u
    let v' := e.symm v
    have heq : mapGraph e G (s(u, v)) = G (s(u', v')) := by
      rw [← e.apply_symm_apply u, ← e.apply_symm_apply v]
      exact mapGraph_equiv_apply e G u' v'
    have hv : 0 < G (s(u', v')) := by
      rw [← heq]
      exact huv
    simpa [u', v'] using h u' v' hv

private abbrev RootOccurrence {V : Type} [Fintype V] (G : MGraph V) (a : V) :=
  {o : Occurrence G // Touches a o.1}

private noncomputable instance rootOccurrenceFintype {V : Type} [Fintype V]
    (G : MGraph V) (a : V) : Fintype (RootOccurrence G a) := Fintype.ofFinite _

private theorem otherEndpoint_ne_root {V : Type} [Fintype V] (G : MGraph V)
    (hloop : Loopless G) (a : V) (o : RootOccurrence G a) :
    otherEndpoint a o.val.1 o.property ≠ a := by
  intro h
  have he : o.val.1 = s(a, otherEndpoint a o.val.1 o.property) :=
    Classical.choose_spec o.property
  have he' : o.val.1 = s(a, a) := by simpa [h] using he
  have hp : 0 < G o.val.1 := Nat.zero_lt_of_lt o.val.2.isLt
  rw [he'] at hp
  exact (Nat.ne_of_gt hp) (hloop a)

private def rootList {V : Type} [Fintype V] (G : MGraph V) (a : V)
    (hloop : Loopless G) :
    List (Outside a) :=
  (Finset.univ : Finset (RootOccurrence G a)).toList.map fun o =>
    ⟨otherEndpoint a o.val.1 o.property, otherEndpoint_ne_root G hloop a o⟩

private theorem rootOccurrence_card {V : Type} [Fintype V] (G : MGraph V) (a : V) :
    Fintype.card (RootOccurrence G a) = degree G a := by
  classical
  calc
    Fintype.card (RootOccurrence G a) =
        Fintype.card (Σ e : {e : Sym2 V // Touches a e}, Fin (G e.val)) :=
      Fintype.card_congr (Equiv.subtypeSigmaEquiv (fun e => Fin (G e)) (fun e => Touches a e))
    _ = ∑ e : {e : Sym2 V // Touches a e}, Fintype.card (Fin (G e.val)) := by simp
    _ = ∑ e : {e : Sym2 V // Touches a e}, G e.val := by simp
    _ = ∑ e : Sym2 V, if Touches a e then G e else 0 := by
      classical
      calc
        (∑ e : {e : Sym2 V // Touches a e}, G e.val) =
            ∑ e ∈ (Finset.univ : Finset (Sym2 V)).filter (Touches a), G e := by
          refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
          · intro x hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
          · intro x hx y hy h
            exact Subtype.ext h
          · intro y hy
            rcases Finset.mem_filter.mp hy with ⟨_, hy⟩
            exact ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩
          · intro x hx
            rfl
        _ = ∑ e : Sym2 V, if Touches a e then G e else 0 := by
          simp [Finset.sum_filter]
    _ = degree G a := by rfl

private theorem rootList_length {V : Type} [Fintype V] (G : MGraph V) (a : V)
    (hloop : Loopless G) : (rootList G a hloop).length = degree G a := by
  classical
  simp [rootList, rootOccurrence_card]

private theorem mapGraph_some_apply {V : Type} [Fintype V] (B : MGraph V) (x y : V) :
    mapGraph some B (s(some x, some y)) = B (s(x, y)) := by
  classical
  unfold mapGraph
  rw [Finset.sum_eq_single (s(x, y))]
  · simp
  · intro e he hne
    have hnot : Sym2.map some e ≠ s(some x, some y) := by
      intro h
      apply hne
      exact (Sym2.map.injective (fun _ _ h => Option.some.inj h)) h
    simp [hnot]
  · simp

private theorem mapGraph_some_zero_if_mixed {V : Type} [Fintype V] (B : MGraph V)
    (e : Sym2 (Option V)) (h : ∀ x y : V, s(some x, some y) ≠ e) :
    mapGraph some B e = 0 := by
  classical
  unfold mapGraph
  apply Finset.sum_eq_zero
  intro x hx
  by_cases he : Sym2.map some x = e
  · exfalso
    induction x using Sym2.ind with
    | h u v => exact (h u v) (by simpa [Sym2.map_mk] using he)
  · simp [he]

private theorem star_root_apply {V : Type} [Fintype V] (a : V) (xs : List (Outside a))
    (b : Outside a) : ThresholdFoundations.star xs (s(none, some b)) = xs.count b := by
  classical
  letI : DecidableEq (Outside a) := Classical.decEq _
  have hpair : ∀ x y : Outside a, s(none, some x) = s(none, some y) ↔ x = y := by
    intro x y
    constructor
    · intro h
      exact Option.some.inj ((Sym2.mkEmbedding none).injective h)
    · rintro rfl
      rfl
  induction xs with
  | nil => simp [ThresholdFoundations.star]
  | cons x xs ih =>
    simp only [ThresholdFoundations.star, List.map_cons, List.count_cons]
    have htail : (List.map (fun v : Outside a => s(none, some v)) xs).count
        (s(none, some b)) = xs.count b := by
      simpa [ThresholdFoundations.star] using ih
    simp [hpair, beq_iff_eq, htail, Subtype.ext_iff]

private theorem star_nonroot_zero {V : Type} [Fintype V] (xs : List V) (x y : V) :
    ThresholdFoundations.star xs (s(some x, some y)) = 0 := by
  classical
  unfold ThresholdFoundations.star
  apply List.count_eq_zero_of_not_mem
  intro hmem
  obtain ⟨z, hz, hzeq⟩ := List.mem_map.mp hmem
  simp [Sym2.eq] at hzeq

private theorem star_root_loop_zero {V : Type} [Fintype V] (xs : List V) :
    ThresholdFoundations.star xs (s(none, none)) = 0 := by
  classical
  unfold ThresholdFoundations.star
  apply List.count_eq_zero_of_not_mem
  intro hmem
  obtain ⟨z, hz, hzeq⟩ := List.mem_map.mp hmem
  simp [Sym2.eq] at hzeq

private theorem rebuild_apply_root {V : Type} [Fintype V] (G : MGraph V) (a : V)
    (xs : List (Outside a)) (b : Outside a) :
    rebuild G a xs (s(a, b.val)) = xs.count b := by
  classical
  have hm : rebuild G a xs (s(a, b.val)) =
      addRoot (outsideGraph G a) xs (s(none, some b)) := by
    unfold rebuild
    have h := mapGraph_equiv_apply (rootEquiv a) (addRoot (outsideGraph G a) xs)
      ((rootEquiv a).symm a) ((rootEquiv a).symm b.val)
    simpa [rootEquiv, rootMap, b.property] using h
  rw [hm]
  change mapGraph some (outsideGraph G a) (s(none, some b)) +
    ThresholdFoundations.star xs (s(none, some b)) = xs.count b
  rw [mapGraph_some_zero_if_mixed, star_root_apply]
  · simp
  · intro x y hxy
    simp [Sym2.eq] at hxy

private theorem rebuild_apply_outside {V : Type} [Fintype V] (G : MGraph V) (a u v : V)
    (hu : u ≠ a) (hv : v ≠ a) (xs : List (Outside a)) :
    rebuild G a xs (s(u, v)) = G (s(u, v)) := by
  classical
  have hu' : (⟨u, hu⟩ : Outside a) = (rootEquiv a).symm u := by
    simp [rootEquiv, hu]
  have hv' : (⟨v, hv⟩ : Outside a) = (rootEquiv a).symm v := by
    simp [rootEquiv, hv]
  have hm : rebuild G a xs (s(u, v)) =
      addRoot (outsideGraph G a) xs (s(some ⟨u, hu⟩, some ⟨v, hv⟩)) := by
    unfold rebuild
    have h := mapGraph_equiv_apply (rootEquiv a) (addRoot (outsideGraph G a) xs)
      ((rootEquiv a).symm u) ((rootEquiv a).symm v)
    simpa [rootEquiv, rootMap, hu, hv] using h
  rw [hm]
  change mapGraph some (outsideGraph G a) (s(some ⟨u, hu⟩, some ⟨v, hv⟩)) +
    ThresholdFoundations.star xs (s(some ⟨u, hu⟩, some ⟨v, hv⟩)) = G (s(u, v))
  rw [mapGraph_some_apply]
  rw [star_nonroot_zero]
  simp [outsideGraph, withoutVertex, Sym2.map_mk]

private theorem rebuild_apply_root_loop {V : Type} [Fintype V] (G : MGraph V) (a : V)
    (xs : List (Outside a)) : rebuild G a xs (s(a, a)) = 0 := by
  classical
  have hm : rebuild G a xs (s(a, a)) =
      addRoot (outsideGraph G a) xs (s(none, none)) := by
    unfold rebuild
    have h := mapGraph_equiv_apply (rootEquiv a) (addRoot (outsideGraph G a) xs)
      ((rootEquiv a).symm a) ((rootEquiv a).symm a)
    simpa [rootEquiv, rootMap] using h
  rw [hm]
  change mapGraph some (outsideGraph G a) (s(none, none)) +
    ThresholdFoundations.star xs (s(none, none)) = 0
  rw [mapGraph_some_zero_if_mixed]
  · rw [star_root_loop_zero]
  · intro x y hxy
    simp [Sym2.eq] at hxy

private theorem rootOccurrence_edge_eq {V : Type} [Fintype V] (G : MGraph V) (a : V)
    (o : RootOccurrence G a) (b : Outside a) :
    o.val.1 = s(a, b.val) ↔ otherEndpoint a o.val.1 o.property = b.val := by
  constructor
  · intro h
    have he := Classical.choose_spec o.property
    have hs : s(a, otherEndpoint a o.val.1 o.property) = s(a, b.val) := he.symm.trans h
    exact (Sym2.mkEmbedding a).injective hs
  · intro h
    have he := Classical.choose_spec o.property
    change Classical.choose o.property = b.val at h
    rw [h] at he
    exact he

private theorem rootList_count {V : Type} [Fintype V] (G : MGraph V) (a : V)
    (hloop : Loopless G) (b : Outside a) :
    (rootList G a hloop).count b = G (s(a, b.val)) := by
  classical
  letI : BEq (RootOccurrence G a) := instBEqOfDecidableEq
  have hcount : (rootList G a hloop).count b =
      Fintype.card {o : RootOccurrence G a //
        otherEndpoint a o.val.1 o.property = b.val} := by
    let l := (Finset.univ : Finset (RootOccurrence G a)).toList
    have hmap : (rootList G a hloop).count b =
        l.countP (fun o => otherEndpoint a o.val.1 o.property = b.val) := by
      simp only [rootList, List.count, List.countP_map]
      congr 1
    rw [hmap]
    rw [← Finset.sum_filter_count_eq_countP]
    calc
      (∑ o ∈ l.toFinset with
          otherEndpoint a o.val.1 o.property = b.val, l.count o) =
          (Finset.univ.filter (fun o : RootOccurrence G a =>
            otherEndpoint a o.val.1 o.property = b.val)).card := by
        rw [show l.toFinset = (Finset.univ : Finset (RootOccurrence G a)) by simp [l]]
        rw [Finset.card_eq_sum_ones]
        apply Finset.sum_congr rfl
        intro o ho
        exact List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp [l])
      _ = Fintype.card {o : RootOccurrence G a //
          otherEndpoint a o.val.1 o.property = b.val} := by
        symm
        exact Fintype.card_subtype _
  rw [hcount]
  let E : {o : RootOccurrence G a //
      otherEndpoint a o.val.1 o.property = b.val} ≃
      {o : Occurrence G // o.1 = s(a, b.val)} :=
    { toFun := fun x => ⟨x.val.val, (rootOccurrence_edge_eq G a x.val b).2 x.property⟩
      invFun := fun x =>
        ⟨⟨x.val, ⟨b.val, x.property⟩⟩,
          (rootOccurrence_edge_eq G a ⟨x.val, ⟨b.val, x.property⟩⟩ b).1 x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl }
  have hcard := Fintype.card_congr E
  rw [hcard]
  let EFin : {o : Occurrence G // o.1 = s(a, b.val)} ≃ Fin (G (s(a, b.val))) :=
    { toFun := fun x => Fin.cast (congrArg G x.property) x.val.2
      invFun := fun i => ⟨⟨s(a, b.val), i⟩, rfl⟩
      left_inv := by
        intro x
        apply Subtype.ext
        cases x with
        | mk o ho => cases o with
          | mk e i => cases ho; rfl
      right_inv := by intro i; simp }
  simpa [EFin] using (Fintype.card_congr EFin)

private theorem rootList_rebuild {V : Type} [Fintype V] (G : MGraph V) (a : V)
    (hloop : Loopless G) : G = rebuild G a (rootList G a hloop) := by
  classical
  funext e
  induction e using Sym2.ind with
  | h u v =>
    by_cases hu : u = a
    · subst u
      by_cases hv : v = a
      · subst v
        rw [hloop a, rebuild_apply_root_loop]
      · let b : Outside a := ⟨v, hv⟩
        calc
          G (s(a, v)) = (rootList G a hloop).count b :=
            (rootList_count G a hloop b).symm
          _ = rebuild G a (rootList G a hloop) (s(a, v)) :=
            (rebuild_apply_root G a (rootList G a hloop) b).symm
    · by_cases hv : v = a
      · subst v
        let b : Outside a := ⟨u, hu⟩
        have hs : s(u, a) = s(a, u) := by simp [Sym2.eq]
        rw [hs]
        calc
          G (s(a, u)) = (rootList G a hloop).count b :=
            (rootList_count G a hloop b).symm
          _ = rebuild G a (rootList G a hloop) (s(a, u)) :=
            (rebuild_apply_root G a (rootList G a hloop) b).symm
      · exact (rebuild_apply_outside G a u v hu hv (rootList G a hloop)).symm

theorem S5_01Statement_of_deps (h01A : ThLean.BP.S5.S5_01AStatement) :
    ThLean.BP.S5.S5_01Statement := by
  intro V hV q hq G hloop a
  let xs := rootList G a hloop
  have hrec : G = rebuild G a xs := by
    simpa [xs] using rootList_rebuild G a hloop
  refine ⟨⟨xs, ?_, hrec⟩, ?_⟩
  · exact rootList_length G a hloop
  · intro ys hys τ
    have hmap : IsColoring q G τ ↔
        IsColoring q (addRoot (outsideGraph G a) ys) (τ ∘ rootEquiv a) := by
      calc
        IsColoring q G τ ↔ IsColoring q (rebuild G a ys) τ :=
          Iff.of_eq (congrArg (fun H : MGraph V => IsColoring q H τ) hys)
        _ ↔ IsColoring q (mapGraph (rootEquiv a)
            (addRoot (outsideGraph G a) ys)) τ := Iff.rfl
        _ ↔ IsColoring q (addRoot (outsideGraph G a) ys) (τ ∘ rootEquiv a) :=
          mapGraph_isColoring_equiv (rootEquiv a) q _ τ
    have hA := h01A (Outside a) q hq (outsideGraph G a) ys
      (τ ∘ rootMap a)
    calc
      IsColoring q G τ ↔
          IsColoring q (outsideGraph G a) (fun v => τ v.val) ∧
            τ a ∉ (ys.map (fun v => τ v.val)).toFinset := by
        rw [hmap]
        simpa [Function.comp_def, rootMap, rootEquiv, List.mem_toFinset,
          List.mem_map, ne_comm] using hA

example (h01A : ThLean.BP.S5.S5_01AStatement) :
    ThLean.BP.S5.S5_01Statement := S5_01Statement_of_deps h01A

end ThLean.W.S561

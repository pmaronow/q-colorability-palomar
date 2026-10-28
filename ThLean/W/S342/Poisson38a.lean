import ThLean.BP.S3.Poisson

noncomputable section
open scoped BigOperators
namespace ThLean.W.S342
universe u
open ThresholdFoundations ThLean.BP.S3
attribute [local instance] Classical.propDecidable
local instance (priority := 100) (α : Type*) : DecidableEq α := Classical.decEq α

variable {V : Type u} [Fintype V]

private lemma sym2_subtype_range {S : Finset V} {x y : V}
    {e : Sym2 {v : V // v ∈ S}}
    (h : Sym2.map Subtype.val e = s(x, y)) : x ∈ S ∧ y ∈ S := by
  revert h
  refine Sym2.inductionOn e ?_
  intro u v h
  simp only [Sym2.map_mk, Sym2.eq_iff] at h
  rcases h with ⟨hux, hvy⟩ | ⟨huy, hvx⟩
  · exact ⟨by rw [← hux]; exact u.property, by rw [← hvy]; exact v.property⟩
  · exact ⟨by rw [← hvx]; exact v.property, by rw [← huy]; exact u.property⟩

private lemma mapGraph_induced_mk (G : MGraph V) (S : Finset V) (x y : V) :
    mapGraph Subtype.val (inducedGraph G S) s(x, y) =
      if x ∈ S ∧ y ∈ S then G s(x, y) else 0 := by
  classical
  unfold mapGraph inducedGraph
  by_cases hxy : x ∈ S ∧ y ∈ S
  · let e₀ : Sym2 {v : V // v ∈ S} := s(⟨x, hxy.1⟩, ⟨y, hxy.2⟩)
    have he₀ : Sym2.map Subtype.val e₀ = s(x, y) := by simp [e₀]
    have hiff : ∀ e : Sym2 {v : V // v ∈ S},
        (Sym2.map Subtype.val e = s(x, y)) ↔ e = e₀ := by
      intro e
      constructor
      · intro he
        apply (Sym2.map.injective Subtype.val_injective)
        calc
          Sym2.map Subtype.val e = s(x, y) := he
          _ = Sym2.map Subtype.val e₀ := he₀.symm
      · rintro rfl
        exact he₀
    have hsum :
        (∑ e : Sym2 {v : V // v ∈ S},
          if Sym2.map Subtype.val e = s(x, y) then
            G (Sym2.map Subtype.val e) else 0) = G s(x, y) := by
      rw [Fintype.sum_eq_single e₀]
      · simp [he₀]
      · intro e hne
        have hnot : Sym2.map Subtype.val e ≠ s(x, y) := by
          intro hh
          apply hne
          apply (Sym2.map.injective Subtype.val_injective)
          calc
            Sym2.map Subtype.val e = s(x, y) := hh
            _ = Sym2.map Subtype.val e₀ := he₀.symm
        simp [hnot]
    simpa [hxy] using hsum
  · simp only [if_neg hxy]
    apply Finset.sum_eq_zero
    intro e he
    by_cases he' : Sym2.map Subtype.val e = s(x, y)
    · exact False.elim (hxy (sym2_subtype_range he'))
    · simp [he']

private lemma neighbor_exists_iff (a : V) (p : Pair V) :
    (∃ v ∈ Finset.univ.erase a, p.val = s(a, v)) ↔ Touches a p.val := by
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, h⟩
  · rintro ⟨v, h⟩
    have hva : v ≠ a := by
      intro hv
      subst v
      exact p.2 a h
    exact ⟨v, by simp [hva], h⟩

private noncomputable def neighborMap (a : V) (S : Finset V) (p : Pair V) : Option V :=
  if h : ∃ v ∈ S, p.val = s(a, v) then some (Classical.choose h) else none

private lemma neighborList_cons (a : V) (S : Finset V) (p : Pair V)
    (w : List (Pair V)) :
    ThLean.BP.S3.neighborList a S (p :: w) =
      (neighborMap a S p).toList ++ ThLean.BP.S3.neighborList a S w := by
  unfold ThLean.BP.S3.neighborList
  rw [List.filterMap_cons]
  by_cases h : ∃ v ∈ S, p.val = s(a, v)
  · simp [neighborMap, h, Option.toList]
  · simp [neighborMap, h, Option.toList]

private lemma listGraph_cons (p : Pair V) (w : List (Pair V)) :
    listGraph (p :: w) = listGraph w + fun e => if p.val = e then 1 else 0 := by
  classical
  funext e
  by_cases h : p.val = e <;> simp [listGraph, h]

private lemma listGraph_loop (a : V) (w : List (Pair V)) :
    listGraph w s(a, a) = 0 := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rw [listGraph_cons]
    have hp : p.val ≠ s(a, a) := p.2 a
    simp [ih, hp]

private lemma degree_listGraph_cons (a : V) (p : Pair V) (w : List (Pair V)) :
    degree (listGraph (p :: w)) a =
      degree (listGraph w) a + if Touches a p.val then 1 else 0 := by
  classical
  rw [listGraph_cons]
  unfold degree
  simp only [Pi.add_apply]
  have hsplit :
      (∑ e, if Touches a e then
        (listGraph w e + (if p.val = e then 1 else 0)) else 0) =
      (∑ e, if Touches a e then listGraph w e else 0) +
      ∑ e, if Touches a e then (if p.val = e then 1 else 0) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases ht : Touches a e <;> simp [ht]
  rw [hsplit]
  congr 1
  rw [Fintype.sum_eq_single p.val]
  · simp
  · intro e hne
    have hne' : p.val ≠ e := fun h => hne h.symm
    simp [hne']

private lemma neighborMap_pos (a : V) (p : Pair V)
    (h : ∃ v ∈ Finset.univ.erase a, p.val = s(a, v)) :
    neighborMap a (Finset.univ.erase a) p = some (Classical.choose h) := by
  unfold neighborMap
  exact dif_pos h

private lemma neighborMap_neg (a : V) (p : Pair V)
    (h : ¬ ∃ v ∈ Finset.univ.erase a, p.val = s(a, v)) :
    neighborMap a (Finset.univ.erase a) p = none := by
  unfold neighborMap
  exact dif_neg h

private lemma neighborList_length_cons (a : V) (p : Pair V) (w : List (Pair V)) :
    (ThLean.BP.S3.neighborList a (Finset.univ.erase a) (p :: w)).length =
      (ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).length +
        if Touches a p.val then 1 else 0 := by
  classical
  rw [neighborList_cons]
  by_cases h : ∃ v ∈ Finset.univ.erase a, p.val = s(a, v)
  · have ht : Touches a p.val := (neighbor_exists_iff a p).mp h
    rw [neighborMap_pos a p h]
    simp [ht, Nat.add_comm]
  · have ht : ¬ Touches a p.val := fun ht => h ((neighbor_exists_iff a p).mpr ht)
    rw [neighborMap_neg a p h]
    simp [ht]

private lemma neighborList_filter_eq_nil (a : V) (S : Finset V) (w : List (Pair V))
    (e : Sym2 V) (h : ∀ v ∈ S, s(a, v) ≠ e) :
    (ThLean.BP.S3.neighborList a S w).filter (fun v => s(a, v) = e) = [] := by
  classical
  induction w with
  | nil => simp [ThLean.BP.S3.neighborList]
  | cons p w ih =>
    rw [neighborList_cons]
    by_cases hp : ∃ v ∈ S, p.val = s(a, v)
    · let v := Classical.choose hp
      have hv : v ∈ S := (Classical.choose_spec hp).1
      have hne : s(a, v) ≠ e := h v hv
      simp [neighborMap, hp, v, hne, ih]
    · simp [neighborMap, hp, ih]

private lemma neighborList_count_mk (a y : V) (w : List (Pair V)) :
    ((ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).filter
      (fun v => s(a, v) = s(a, y))).length = listGraph w s(a, y) := by
  classical
  induction w with
  | nil => simp [ThLean.BP.S3.neighborList, listGraph]
  | cons p w ih =>
    by_cases hya : y = a
    · subst y
      have hloop : ∀ v ∈ Finset.univ.erase a, s(a, v) ≠ s(a, a) := by
        intro v hv hEq
        have hva : v ≠ a := by simpa using hv
        have hvEq : v = a := (Sym2.congr_right).mp hEq
        exact hva hvEq
      have hnil := neighborList_filter_eq_nil a (Finset.univ.erase a) (p :: w)
        (s(a, a)) hloop
      rw [hnil]
      simpa using (listGraph_loop a (p :: w)).symm
    · rw [neighborList_cons]
      have hs : ∀ v, (s(a, v) = s(a, y)) ↔ v = y := by
        intro v
        constructor
        · intro he
          rcases (Sym2.eq_iff).mp he with ⟨_, hvy⟩ | ⟨hay, _⟩
          · exact hvy
          · exact False.elim (hya hay.symm)
        · intro hvy
          rw [hvy]
      by_cases hp : ∃ v ∈ Finset.univ.erase a, p.val = s(a, v)
      · let c := Classical.choose hp
        have hv := Classical.choose_spec hp
        have hsource : (p.val = s(a, y)) ↔ c = y := by
          constructor
          · intro hpy
            exact (hs c).mp (hv.2.symm.trans hpy)
          · intro hcy
            rw [← hcy]
            exact hv.2
        have ih' : ((ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).filter
            (fun z => z = y)).length = listGraph w s(a, y) := by
          simpa [hs] using ih
        have hmap : neighborMap a (Finset.univ.erase a) p = some c := by
          unfold neighborMap
          rw [dif_pos hp]
        rw [hmap]
        simp only [Option.toList_some, List.singleton_append]
        simp only [hs]
        have hfilter :
            (([c] ++ ThLean.BP.S3.neighborList a
              (Finset.univ.erase a) w).filter (fun z => z = y)).length =
              (if c = y then 1 else 0) +
                ((ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).filter
                  (fun z => z = y)).length := by
          by_cases hcy : c = y
          · simp [hcy, Nat.add_comm]
          · simp [hcy]
        calc
          (([c] ++ ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).filter
            (fun z => z = y)).length = (if c = y then 1 else 0) +
              ((ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).filter
                (fun z => z = y)).length := hfilter
          _ = listGraph w s(a, y) + (if c = y then 1 else 0) := by
            rw [ih']
            omega
          _ = listGraph (p :: w) s(a, y) := by
            rw [listGraph_cons]
            simp [hsource]
      · have hsource : p.val ≠ s(a, y) := by
          intro hpy
          exact hp ⟨y, by simp [hya], hpy⟩
        have ih' : ((ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).filter
            (fun z => z = y)).length = listGraph w s(a, y) := by
          simpa [hs] using ih
        rw [neighborMap_neg a p hp]
        simp [hs, hsource, ih', listGraph_cons]

private noncomputable def neighborGraph (a : V) (w : List (Pair V)) : MGraph V :=
  fun e => ((ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).filter
    (fun v => s(a, v) = e)).length

private lemma listGraph_decomposition (a : V) (w : List (Pair V)) :
    listGraph w = mapGraph Subtype.val
      (inducedGraph (listGraph w) (Finset.univ.erase a)) + neighborGraph a w := by
  classical
  funext e
  change listGraph w e = mapGraph Subtype.val
    (inducedGraph (listGraph w) (Finset.univ.erase a)) e +
      ((ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).filter
        (fun v => s(a, v) = e)).length
  refine Sym2.inductionOn e ?_
  intro x y
  by_cases hx : x = a
  · subst x
    by_cases hy : y = a
    · subst y
      rw [mapGraph_induced_mk, neighborList_count_mk]
      simp [Finset.mem_erase]
    · rw [mapGraph_induced_mk, neighborList_count_mk]
      simp [Finset.mem_erase, hy]
  · by_cases hy : y = a
    · subst y
      rw [Sym2.eq_swap (a := x) (b := a)]
      rw [mapGraph_induced_mk, neighborList_count_mk]
      simp [Finset.mem_erase, hx]
    · rw [mapGraph_induced_mk]
      have hnone : ∀ v ∈ Finset.univ.erase a, s(a, v) ≠ s(x, y) := by
        intro v hv heq
        rcases (Sym2.eq_iff).mp heq with ⟨hax, hvy⟩ | ⟨hay, hvx⟩
        · exact hx hax.symm
        · exact hy hay.symm
      have hnil := neighborList_filter_eq_nil a (Finset.univ.erase a) w
        (s(x, y)) hnone
      rw [hnil]
      simp [Finset.mem_erase, hx, hy]

theorem S3_38aStatement_holds : ThLean.BP.S3.S3_38aStatement := by
  intro V _ a w
  constructor
  · induction w with
    | nil => simp [degree, listGraph, ThLean.BP.S3.neighborList]
    | cons p w ih =>
      rw [degree_listGraph_cons, neighborList_length_cons]
      exact congrArg (fun n : ℕ => n + if Touches a p.val then 1 else 0) ih
  · change listGraph w = mapGraph Subtype.val
      (inducedGraph (listGraph w) (Finset.univ.erase a)) +
        (fun e => ((ThLean.BP.S3.neighborList a (Finset.univ.erase a) w).filter
          (fun v => s(a, v) = e)).length)
    exact listGraph_decomposition a w

end ThLean.W.S342

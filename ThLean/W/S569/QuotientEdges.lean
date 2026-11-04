module

public import ThLean.BP.S5.Structure

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S5
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S569

private lemma fiber_cross {V : Type} [Fintype V] (Z : Finset V) (v : V) (hv : v ∉ Z)
    (e : Sym2 V) :
    Sym2.map (identifyVertex Z) e = s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z})) ↔
      ∃ a ∈ Z, e = s(a, v) := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hx : x ∈ Z <;> by_cases hy : y ∈ Z <;>
      simp [Sym2.map_mk, identifyVertex, hx, hy] <;> aesop

section MapGraphDecisions
local instance (priority := 10000) quotientVerticesDecEq {V : Type} (Z : Finset V) :
    DecidableEq (QuotientVertices Z) := fun a b => Classical.propDecidable (a = b)

private lemma sum_cross {V : Type} [Fintype V] (G : MGraph V) (Z : Finset V)
    (v : V) (hv : v ∉ Z) :
    (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e =
      s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z})) then G e else 0) =
      ∑ a ∈ Z, G s(a, v) := by

  let fiber : Finset (Sym2 V) := Finset.univ.filter (fun e =>
    Sym2.map (identifyVertex Z) e = s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z})))
  rw [show (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e =
      s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z})) then G e else 0) =
      ∑ e ∈ fiber, G e by simp [fiber, Finset.sum_filter]]
  apply Finset.sum_bij (fun e he => Classical.choose ((fiber_cross Z v hv e).mp (by simpa [fiber] using he)))
  · intro e he
    have hp : Sym2.map (identifyVertex Z) e = s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z})) := by
      simpa [fiber] using he
    exact ((fiber_cross Z v hv e).mp hp).choose_spec.1
  · intro e₁ he₁ e₂ he₂ hi
    have hp₁ : Sym2.map (identifyVertex Z) e₁ = s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z})) := by
      simpa [fiber] using he₁
    have hp₂ : Sym2.map (identifyVertex Z) e₂ = s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z})) := by
      simpa [fiber] using he₂
    have h₁ := (fiber_cross Z v hv e₁).mp hp₁
    have h₂ := (fiber_cross Z v hv e₂).mp hp₂
    calc
      e₁ = s(Classical.choose h₁, v) := h₁.choose_spec.2
      _ = s(Classical.choose h₂, v) := by rw [hi]
      _ = e₂ := h₂.choose_spec.2.symm
  · intro a ha
    refine ⟨s(a, v), ?_, ?_⟩
    · simpa [fiber] using (fiber_cross Z v hv (s(a, v))).mpr ⟨a, ha, rfl⟩
    · have hp : Sym2.map (identifyVertex Z) (s(a, v)) = s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z})) :=
        (fiber_cross Z v hv (s(a, v))).mpr ⟨a, ha, rfl⟩
      have hs := Classical.choose_spec ((fiber_cross Z v hv (s(a, v))).mp hp)
      have heq : s(a, v) = s(Classical.choose ((fiber_cross Z v hv (s(a, v))).mp hp), v) := hs.2
      have heq' := Sym2.eq_iff.mp heq
      rcases heq' with ⟨h, _⟩ | ⟨h, h'⟩
      · exact h.symm
      · exact (hv (h ▸ ha)).elim
  · intro e he
    have hp : Sym2.map (identifyVertex Z) e = s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z})) := by
      simpa [fiber] using he
    exact congrArg G ((fiber_cross Z v hv e).mp hp).choose_spec.2


private lemma fiber_root {V : Type} [Fintype V] (Z : Finset V) (e : Sym2 V) :
    Sym2.map (identifyVertex Z) e = s(none, none) ↔
      ∃ a ∈ Z, ∃ b ∈ Z, e = s(a, b) := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hx : x ∈ Z <;> by_cases hy : y ∈ Z <;>
      simp [Sym2.map_mk, identifyVertex, hx, hy] <;> aesop

private lemma sum_root_zero {V : Type} [Fintype V] (G : MGraph V) (Z : Finset V)
    (hint : ∀ a ∈ Z, ∀ b ∈ Z, G s(a, b) = 0) :
    (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e = s(none, none) then G e else 0) = 0 := by

  rw [show (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e = s(none, none) then G e else 0) =
      ∑ e ∈ Finset.univ.filter (fun e => Sym2.map (identifyVertex Z) e = s(none, none)), G e by
      simp [Finset.sum_filter]]
  apply Finset.sum_eq_zero
  intro e he
  have hp := (fiber_root Z e).mp (Finset.mem_filter.mp he |>.2)
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  exact hint a ha b hb

private lemma fiber_out {V : Type} [Fintype V] (Z : Finset V)
    (u v : V) (hu : u ∉ Z) (hv : v ∉ Z) (e : Sym2 V) :
    Sym2.map (identifyVertex Z) e =
      s(some (⟨u, hu⟩ : {v : V // v ∉ Z}), some (⟨v, hv⟩ : {v : V // v ∉ Z})) ↔
      e = s(u, v) := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hx : x ∈ Z <;> by_cases hy : y ∈ Z <;>
      simp [Sym2.map_mk, identifyVertex, hx, hy] <;> aesop

private lemma sum_out {V : Type} [Fintype V] (G : MGraph V) (Z : Finset V)
    (u v : V) (hu : u ∉ Z) (hv : v ∉ Z) :
    (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e =
      s(some (⟨u, hu⟩ : {v : V // v ∉ Z}), some (⟨v, hv⟩ : {v : V // v ∉ Z})) then G e else 0) =
      G s(u, v) := by

  rw [show (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e =
      s(some (⟨u, hu⟩ : {v : V // v ∉ Z}), some (⟨v, hv⟩ : {v : V // v ∉ Z})) then G e else 0) =
      ∑ e ∈ Finset.univ.filter (fun e => Sym2.map (identifyVertex Z) e =
        s(some (⟨u, hu⟩ : {v : V // v ∉ Z}), some (⟨v, hv⟩ : {v : V // v ∉ Z}))), G e by
      simp [Finset.sum_filter]]
  simp only [Finset.sum_filter]
  simp_rw [fiber_out Z u v hu hv]
  simp



end MapGraphDecisions

private lemma map_some_fiber {X : Type} [Fintype X] (u v : X) (e : Sym2 X) :
    Sym2.map some e = s(some u, some v) ↔ e = s(u, v) := by
  constructor
  · intro h
    exact Sym2.map.injective (fun _ _ hxy => Option.some.inj hxy) h
  · rintro rfl
    rfl

private lemma map_some_root_ne {X : Type} (e : Sym2 X) :
    Sym2.map some e ≠ s(none, none) := by
  induction e using Sym2.ind with
  | h x y => simp [Sym2.map_mk]

private lemma map_some_cross_ne {X : Type} (v : X) (e : Sym2 X) :
    Sym2.map some e ≠ s(none, some v) := by
  induction e using Sym2.ind with
  | h x y => simp [Sym2.map_mk]

section StarDecisions
variable {V : Type}
local instance (priority := 10000) outsideDecEq (Z : Finset V) :
    DecidableEq {v : V // v ∉ Z} :=
  fun a b => Classical.propDecidable (a = b)

private lemma star_root_root [Fintype V] (Z : Finset V)
    (xs : List {v : V // v ∉ Z}) :
    ThresholdFoundations.star xs (s(none, none)) = 0 := by
  unfold ThresholdFoundations.star
  rw [List.count_eq_zero]
  intro hmem
  rcases List.mem_map.mp hmem with ⟨x, hx, heq⟩
  have : s(none, some x) = s(none, none) := heq
  simp at this

private lemma star_cross [Fintype V] (Z : Finset V)
    (xs : List {v : V // v ∉ Z}) (v : V) (hv : v ∉ Z) :
    ThresholdFoundations.star xs (s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z}))) =
      xs.count (⟨v, hv⟩ : {v : V // v ∉ Z}) := by
  unfold ThresholdFoundations.star
  have hf : Function.Injective (fun x : {v : V // v ∉ Z} => s(none, some x)) := by
    intro a b hab
    have hh := Sym2.eq_iff.mp hab
    rcases hh with ⟨_, h⟩ | ⟨h, _⟩
    · exact Option.some.inj h
    · cases h
  exact List.count_map_of_injective xs (fun x => s(none, some x)) hf ⟨v, hv⟩

private lemma star_out [Fintype V] (Z : Finset V)
    (xs : List {v : V // v ∉ Z}) (u v : V) (hu : u ∉ Z) (hv : v ∉ Z) :
    ThresholdFoundations.star xs
      (s(some (⟨u, hu⟩ : {v : V // v ∉ Z}), some (⟨v, hv⟩ : {v : V // v ∉ Z}))) = 0 := by
  unfold ThresholdFoundations.star
  rw [List.count_eq_zero]
  intro hmem
  rcases List.mem_map.mp hmem with ⟨x, hx, heq⟩
  have : s(none, some x) =
      s(some (⟨u, hu⟩ : {v : V // v ∉ Z}), some (⟨v, hv⟩ : {v : V // v ∉ Z})) := heq
  simp at this

private lemma rhs_root_root [Fintype V] (G : MGraph V) (Z : Finset V)
    (xs : List {v : V // v ∉ Z}) :
    addRoot (fun e => G (Sym2.map Subtype.val e)) xs (s(none, none)) = 0 := by
  rw [ThresholdFoundations.addRoot, Pi.add_apply, star_root_root]
  simp [mapGraph, map_some_root_ne]

private lemma rhs_cross [Fintype V] (G : MGraph V) (Z : Finset V)
    (xs : List {v : V // v ∉ Z}) (v : V) (hv : v ∉ Z) :
    addRoot (fun e => G (Sym2.map Subtype.val e)) xs
      (s(none, some (⟨v, hv⟩ : {v : V // v ∉ Z}))) =
      xs.count (⟨v, hv⟩ : {v : V // v ∉ Z}) := by
  rw [ThresholdFoundations.addRoot, Pi.add_apply, star_cross]
  simp [mapGraph, map_some_cross_ne]

private lemma rhs_out [Fintype V] (G : MGraph V) (Z : Finset V)
    (xs : List {v : V // v ∉ Z}) (u v : V) (hu : u ∉ Z) (hv : v ∉ Z) :
    addRoot (fun e => G (Sym2.map Subtype.val e)) xs
      (s(some (⟨u, hu⟩ : {v : V // v ∉ Z}), some (⟨v, hv⟩ : {v : V // v ∉ Z}))) =
      G s(u, v) := by
  rw [ThresholdFoundations.addRoot, Pi.add_apply, star_out]
  simp [mapGraph, map_some_fiber]
end StarDecisions

set_option linter.style.haveILetI false in
theorem S5_07Statement_holds : ThLean.BP.S5.S5_07Statement := by
  intro V hV G hloop Z hZ hinter xs hcount
  letI : DecidableEq (QuotientVertices Z) := fun a b => Classical.propDecidable (a = b)
  funext e
  induction e using Sym2.ind with
  | h a b =>
    cases a with
    | none =>
      cases b with
      | none =>
        change mapGraph (identifyVertex Z) G (s(none, none)) = _
        change (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e = s(none, none) then G e else 0) = _
        calc
          mapGraph (identifyVertex Z) G (s(none, none)) = 0 := sum_root_zero G Z hinter
          _ = addRoot (fun e => G (Sym2.map Subtype.val e)) xs (s(none, none)) :=
            (rhs_root_root G Z xs).symm
      | some v =>
        change mapGraph (identifyVertex Z) G (s(none, some v)) = _
        change (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e = s(none, some v) then G e else 0) = _
        calc
          mapGraph (identifyVertex Z) G (s(none, some v)) =
              ∑ a ∈ Z, G s(a, v.val) := sum_cross G Z v.val v.property
          _ = xs.count v := (hcount v).symm
          _ = addRoot (fun e => G (Sym2.map Subtype.val e)) xs (s(none, some v)) :=
            (rhs_cross G Z xs v.val v.property).symm
    | some u =>
      cases b with
      | none =>
        have hswap : s(some u, none) = s(none, some u) := by simp
        simp only [hswap]
        change mapGraph (identifyVertex Z) G (s(none, some u)) = _
        change (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e = s(none, some u) then G e else 0) = _
        calc
          mapGraph (identifyVertex Z) G (s(none, some u)) =
              ∑ a ∈ Z, G s(a, u.val) := sum_cross G Z u.val u.property
          _ = xs.count u := (hcount u).symm
          _ = addRoot (fun e => G (Sym2.map Subtype.val e)) xs (s(none, some u)) :=
            (rhs_cross G Z xs u.val u.property).symm
      | some v =>
        change mapGraph (identifyVertex Z) G (s(some u, some v)) = _
        change (∑ e : Sym2 V, if Sym2.map (identifyVertex Z) e = s(some u, some v) then G e else 0) = _
        calc
          mapGraph (identifyVertex Z) G (s(some u, some v)) = G s(u.val, v.val) :=
            sum_out G Z u.val v.val u.property v.property
          _ = addRoot (fun e => G (Sym2.map Subtype.val e)) xs (s(some u, some v)) :=
            (rhs_out G Z xs u.val v.val u.property v.property).symm

example : ThLean.BP.S5.S5_07Statement := S5_07Statement_holds

end ThLean.W.S569

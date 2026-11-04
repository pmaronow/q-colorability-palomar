module

public import ThLean.BP.S5.Identification

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S523S
open ThresholdFoundations ThLean.BP.S5

theorem indicator_bounds (P : Prop) : 0 ≤ indicator P ∧ |indicator P| ≤ 1 := by
  classical
  by_cases h : P <;> simp [indicator, h]

def countsList {V : Type} [Fintype V] (c : V → ℕ) : List V :=
  (∑ v, Multiset.replicate (c v) v).toList

theorem countsList_count {V : Type} [Fintype V] [BEq V] [LawfulBEq V] (c : V → ℕ) (v : V) :
    (countsList c).count v = c v := by
  classical
  have hc : List.count v (countsList c) = Multiset.count v (↑(countsList c) : Multiset V) := by
    simp only [List.count, Multiset.count, Multiset.coe_countP]
    congr 1
    funext a
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, eq_comm (a := a)]
  rw [hc, countsList, Multiset.coe_toList]
  simp [Multiset.count_sum', Multiset.count_replicate]

theorem countsList_ofFn {V : Type} [Fintype V] [BEq V] [LawfulBEq V]
    {n : ℕ} (x : Fin n → V) (v : V) :
    (List.ofFn x).count v = (Finset.univ.filter (fun i => x i = v)).card := by
  classical
  have hc : (List.ofFn x).count v = ∑ i : Fin n, if x i = v then 1 else 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
      by_cases h : x 0 = v <;> simp [h, beq_iff_eq, Nat.add_comm]
  simpa [← Finset.sum_filter] using hc

theorem sym2_val_injective {V : Type} {p : V → Prop} :
    Function.Injective (Sym2.map (Subtype.val : Subtype p → V)) := by
  intro e d h
  induction e using Sym2.ind with | h a b =>
    induction d using Sym2.ind with | h c d =>
      simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩

theorem mapGraph_val_eval {V : Type} {p : V → Prop} [Fintype V] [Fintype (Subtype p)]
    (B : MGraph (Subtype p)) (e : Sym2 (Subtype p)) :
    mapGraph Subtype.val B (Sym2.map Subtype.val e) = B e := by
  classical
  simp [mapGraph, sym2_val_injective.eq_iff]

def crossGraph {V : Type} [Fintype V] (Z : Finset V)
    (c : ({v : V // v ∈ Z} × {v : V // v ∉ Z}) → ℕ) : MGraph V :=
  fun e => ∑ p, if e = s(p.1.val, p.2.val) then c p else 0

theorem inside_ne_outside {V : Type} (Z : Finset V)
    (a : {v : V // v ∈ Z}) (v : {v : V // v ∉ Z}) : a.val ≠ v.val := by
  intro h
  exact v.property (h ▸ a.property)

theorem crossGraph_outside {V : Type} [Fintype V] (Z : Finset V)
    (c : ({v : V // v ∈ Z} × {v : V // v ∉ Z}) → ℕ)
    (u v : {v : V // v ∉ Z}) : crossGraph Z c s(u.val, v.val) = 0 := by
  classical
  unfold crossGraph
  apply Finset.sum_eq_zero
  intro p _
  have h1 := (inside_ne_outside Z p.1 u).symm
  have h2 := (inside_ne_outside Z p.1 v).symm
  simp [h1, h2]

theorem crossGraph_inside {V : Type} [Fintype V] (Z : Finset V)
    (c : ({v : V // v ∈ Z} × {v : V // v ∉ Z}) → ℕ)
    (u v : {v : V // v ∈ Z}) : crossGraph Z c s(u.val, v.val) = 0 := by
  classical
  unfold crossGraph
  apply Finset.sum_eq_zero
  intro p _
  simp [inside_ne_outside Z u p.2, inside_ne_outside Z v p.2]

theorem crossGraph_cross {V : Type} [Fintype V] (Z : Finset V)
    (c : ({v : V // v ∈ Z} × {v : V // v ∉ Z}) → ℕ)
    (a : {v : V // v ∈ Z}) (v : {v : V // v ∉ Z}) :
    crossGraph Z c s(a.val, v.val) = c (a, v) := by
  classical
  unfold crossGraph
  have he (p : {v : V // v ∈ Z} × {v : V // v ∉ Z}) :
      s(a.val, v.val) = s(p.1.val, p.2.val) ↔ p = (a, v) := by
    rw [Sym2.eq_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)
      · exact False.elim ((inside_ne_outside Z a p.2) h1)
    · rintro rfl
      exact Or.inl ⟨rfl, rfl⟩
  simp_rw [he]
  simp

theorem mapGraph_outside_inside {V : Type} [Fintype V] (Z : Finset V)
    (B : MGraph {v : V // v ∉ Z}) (a : {v : V // v ∈ Z}) (v : V) :
    mapGraph Subtype.val B s(a.val, v) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  induction e using Sym2.ind with | h x y =>
    simp [Sym2.map_mk, (inside_ne_outside Z a x).symm,
      (inside_ne_outside Z a y).symm]

theorem split_event_bound (h07 : S5_07Statement)
    {V : Type} [Fintype V] (q : ℕ) (Z : Finset V) (hZ : Z.Nonempty)
    (B : MGraph {v : V // v ∉ Z}) (R : MGraph {v : V // v ∈ Z})
    (c : ({v : V // v ∈ Z} × {v : V // v ∉ Z}) → ℕ) :
    let G := mapGraph Subtype.val B + mapGraph Subtype.val R + crossGraph Z c
    indicator (Colorable q G ∧ ¬ Colorable q (identify G Z)) ≤
      indicator (R ≠ 0) + indicator (Colorable q B ∧
        ¬ Colorable q (addRoot B (countsList (fun v => ∑ a, c (a, v))))) := by
  classical
  dsimp only
  by_cases hR : R = 0
  · subst R
    have hm0 : mapGraph (Subtype.val : {v : V // v ∈ Z} → V) 0 = 0 := by
      ext e
      simp [mapGraph]
    simp only [hm0, add_zero, ne_eq, not_true_eq_false, indicator, ite_false, zero_add]
    split_ifs with hG hB
    · rfl
    · exfalso
      let G := mapGraph Subtype.val B + crossGraph Z c
      have hout (u v : {v : V // v ∉ Z}) : G s(u.val, v.val) = B s(u, v) := by
        change mapGraph Subtype.val B (Sym2.map Subtype.val s(u, v)) +
          crossGraph Z c s(u.val, v.val) = _
        rw [mapGraph_val_eval, crossGraph_outside, add_zero]
      have hcol : Colorable q B := by
        obtain ⟨σ, hσ⟩ := hG.1
        refine ⟨fun v => σ v.val, fun u v h => hσ u.val v.val ?_⟩
        change 0 < G s(u.val, v.val)
        rw [hout]
        exact h
      have hloop : Loopless G := by
        intro v
        obtain ⟨σ, hσ⟩ := hG.1
        by_contra h
        exact hσ v v (Nat.pos_of_ne_zero h) rfl
      have hin (u : V) (hu : u ∈ Z) (v : V) (hv : v ∈ Z) : G s(u, v) = 0 := by
        simpa [G, crossGraph_inside Z c ⟨u, hu⟩ ⟨v, hv⟩] using
          mapGraph_outside_inside Z B ⟨u, hu⟩ v
      have hc (v : {v : V // v ∉ Z}) :
          (countsList (fun v => ∑ a, c (a, v))).count v = ∑ a ∈ Z, G s(a, v.val) := by
        rw [countsList_count]
        calc
          (∑ a, c (a, v)) = ∑ a : {v : V // v ∈ Z}, G s(a.val, v.val) := by
            apply Finset.sum_congr rfl
            intro a _
            simp [G, mapGraph_outside_inside, crossGraph_cross]
          _ = ∑ a ∈ Z, G s(a, v.val) := Finset.sum_coe_sort Z (fun a => G s(a, v.val))
      have hid := h07 V G hloop Z hZ hin _ hc
      have hb : (fun e => G (Sym2.map Subtype.val e)) = B := by
        funext e
        induction e using Sym2.ind with | h u v => exact hout u v
      rw [hb] at hid
      exact hB ⟨hcol, by simpa only [← hid] using hG.2⟩
    · positivity
    · rfl
  · have hI := (indicator_bounds (Colorable q B ∧
      ¬ Colorable q (addRoot B (countsList (fun v => ∑ a, c (a, v)))))).1
    have hG := (abs_le.mp (indicator_bounds
      (Colorable q (mapGraph Subtype.val B + mapGraph Subtype.val R + crossGraph Z c) ∧
        ¬ Colorable q (identify
          (mapGraph Subtype.val B + mapGraph Subtype.val R + crossGraph Z c) Z))).2).2
    simpa [indicator, hR] using (le_add_of_le_of_nonneg hG hI)

end ThLean.W.S523S

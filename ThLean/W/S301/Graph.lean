import ThLean.BP.S3.Graph

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v

namespace ThLean.W.S301
open ThresholdFoundations

private def sym2RelabelEquiv {V : Type u} {W : Type v}
    (π : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map π
  invFun := Sym2.map π.symm
  left_inv x := by
    rw [Sym2.map_map]
    simp
  right_inv x := by
    rw [Sym2.map_map]
    simp

private theorem relabel_apply {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] (π : V ≃ W) (G : MGraph V) (e' : Sym2 W) :
    relabel π G e' = G (Sym2.map π.symm e') := by
  classical
  unfold relabel mapGraph
  rw [Fintype.sum_eq_single (Sym2.map π.symm e')]
  · simp [Sym2.map_map]
  · intro e he
    have hne : Sym2.map π e ≠ e' := by
      intro h
      apply he
      apply (Sym2.map.injective π.injective)
      calc
        Sym2.map π e = e' := h
        _ = Sym2.map π (Sym2.map π.symm e') := by simp [Sym2.map_map]
    simp [hne]

private theorem touches_relabel_iff {V : Type u} {W : Type v}
    (π : V ≃ W) (u : V) (e : Sym2 V) :
    Touches (π u) (Sym2.map π e) ↔ Touches u e := by
  unfold Touches
  constructor
  · rintro ⟨w, hw⟩
    have heq : Sym2.map π e = Sym2.map π (s(u, π.symm w)) := by
      simpa using hw
    exact ⟨π.symm w, (Sym2.map.injective π.injective) heq⟩
  · rintro ⟨v, rfl⟩
    exact ⟨π v, by simp [Sym2.map_mk]⟩

theorem S3_01Statement_holds : ThLean.BP.S3.S3_01Statement := by
  intro V W _ _ q hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G a b hab σ
    have hpos (x y : V) :
        0 < addEdge G (s(a,b)) (s(x,y)) ↔
          0 < G (s(x,y)) ∨ s(x,y) = s(a,b) := by
      by_cases hxy : s(x,y) = s(a,b)
      · unfold addEdge
        rw [Function.update_apply]
        simp [hxy]
      · unfold addEdge
        rw [Function.update_apply]
        simp [hxy]
    constructor
    · intro h
      refine ⟨?_, h a b (by simp [addEdge])⟩
      intro x y hG
      exact h x y ((hpos x y).2 (Or.inl hG))
    · rintro ⟨hG, habσ⟩ x y hxy
      rcases (hpos x y).1 hxy with hGxy | heq
      · exact hG x y hGxy
      · rcases Sym2.eq_iff.mp heq with hsame | hswap
        · rcases hsame with ⟨rfl, rfl⟩
          exact habσ
        · rcases hswap with ⟨rfl, rfl⟩
          simpa [ne_comm] using habσ
  · intro G H hGH σ hσ
    simp only [colorings, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    intro a b hab
    exact hσ a b (lt_of_lt_of_le hab (hGH (s(a,b))))
  · intro G
    classical
    ext σ
    simp only [colorings, Finset.mem_filter, Finset.mem_univ, true_and]
    have hpos (a b : V) :
        0 < simpleGraph (edgeSupport G) (s(a,b)) ↔ 0 < G (s(a,b)) := by
      by_cases hG : 0 < G (s(a,b))
      · simp [simpleGraph, edgeSupport, hG]
      · simp [simpleGraph, edgeSupport, hG]
    constructor
    · intro h a b hab
      exact h a b ((hpos a b).2 hab)
    · intro h a b hab
      exact h a b ((hpos a b).1 hab)
  · intro G π σ
    constructor
    · intro h a b hab
      have hrel : 0 < relabel π G (s(π a, π b)) := by
        rw [relabel_apply]
        simpa [Sym2.map_mk] using hab
      have hcol := h (π a) (π b) hrel
      simpa using hcol
    · intro h a b hab
      have hsrc : 0 < G (s(π.symm a, π.symm b)) := by
        simpa [relabel_apply, Sym2.map_mk] using hab
      have hcol := h (π.symm a) (π.symm b) hsrc
      simpa using hcol
  · intro G π a
    classical
    unfold degree
    let eπ := sym2RelabelEquiv π
    have hsum := Fintype.sum_equiv eπ
      (fun e : Sym2 V =>
        if Touches (π a) (Sym2.map π e) then relabel π G (Sym2.map π e) else 0)
      (fun e' : Sym2 W =>
        if Touches (π a) e' then relabel π G e' else 0)
      (by intro e; rfl)
    calc
      (∑ e' : Sym2 W, if Touches (π a) e' then relabel π G e' else 0) =
          ∑ e : Sym2 V,
            if Touches (π a) (Sym2.map π e) then relabel π G (Sym2.map π e) else 0 := hsum.symm
      _ = ∑ e : Sym2 V, if Touches a e then G e else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases ht : Touches a e
        · rw [touches_relabel_iff, relabel_apply]
          rw [Sym2.map_map]
          simp
        · rw [touches_relabel_iff, relabel_apply]
          rw [Sym2.map_map]
          simp
  · intro G e hG
    unfold addPair erasePair addEdge eraseEdge
    funext f
    by_cases hf : f = e.val
    · subst f
      have hle : 1 ≤ G e.val := by omega
      simp [Nat.sub_add_cancel hle]
    · simp [Function.update_of_ne hf]
  · refine ⟨fun _ => (⟨0, by omega⟩ : Fin q), ?_⟩
    simp [IsColoring]

end ThLean.W.S301

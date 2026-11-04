module

public import ThLean.BP.S6.Foundation

@[expose] public section

noncomputable section
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S609

private theorem coloring_addPair_iff {n q : ℕ} (G : ThLean.BP.S6.Graph n) (u y : Fin n)
    (e : ThLean.BP.S6.Edge n) (he : e.val = s(u, y)) (σ : Fin n → Fin q) :
    IsColoring q (addPair G e) σ ↔ IsColoring q G σ ∧ σ u ≠ σ y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply h a b
      have hle : G (s(a, b)) ≤ addPair G e (s(a, b)) := by
        by_cases hEq : s(a, b) = e.val
        · rw [hEq]
          simp [addPair, addEdge]
        · simp [addPair, addEdge, hEq]
      exact lt_of_lt_of_le hab hle
    · apply h u y
      have hpos : 0 < addPair G e (s(u, y)) := by
        simp [addPair, addEdge, he]
      exact hpos
  · rintro ⟨hG, hne⟩ a b hab
    by_cases hEq : s(a, b) = e.val
    · have hPair : s(a, b) = s(u, y) := hEq.trans he
      rcases Sym2.eq_iff.mp hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne
      · exact Ne.symm hne
    · have hOld : 0 < G (s(a, b)) := by
        have hupdate : addPair G e (s(a, b)) = G (s(a, b)) := by
          simp [addPair, addEdge, hEq]
        rw [hupdate] at hab
        exact hab
      exact hG a b hOld

theorem S6_06Statement_holds : ThLean.BP.S6.S6_06Statement := by
  intro n q hn hq G u y hG hy
  have hyNotFrozen : ¬ Frozen q G u y := by
    simpa [frozenClass] using hy
  have hneqWitness : ∃ σ, IsColoring q G σ ∧ σ u ≠ σ y := by
    by_contra h
    have hfreeze : ∀ σ, IsColoring q G σ → σ u = σ y := by
      intro σ hσ
      by_contra hne
      exact h ⟨σ, hσ, hne⟩
    exact hyNotFrozen ⟨hG, hfreeze⟩
  have hyNe : y ≠ u := by
    intro hyu
    subst y
    obtain ⟨σ, hσ, hne⟩ := hneqWitness
    exact hne (rfl)
  refine ⟨hyNe, ?_⟩
  intro e he
  have hColorableAdd : Colorable q (addPair G e) := by
    obtain ⟨σ, hσ, hne⟩ := hneqWitness
    exact ⟨σ, (coloring_addPair_iff G u y e he σ).2 ⟨hσ, hne⟩⟩
  have hfreezeIff : ∀ v, Frozen q (addPair G e) u v ↔
      Frozen q G u v ∨ (y, v) ∈ relation q G u := by
    intro v
    constructor
    · rintro ⟨_, hnew⟩
      by_cases hv : Frozen q G u v
      · exact Or.inl hv
      · right
        simp only [relation, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hG, hyNotFrozen, hv, ?_⟩
        intro σ hσ
        by_cases hUy : σ u = σ y
        · exact Or.inl hUy
        · have hσAdd : IsColoring q (addPair G e) σ :=
            (coloring_addPair_iff G u y e he σ).2 ⟨hσ, hUy⟩
          exact Or.inr (hnew σ hσAdd)
    · intro h
      rcases h with hv | hrel
      · exact ⟨hColorableAdd, fun σ hσ =>
          hv.2 σ ((coloring_addPair_iff G u y e he σ).1 hσ).1⟩
      · have hrel' := hrel
        simp only [relation, Finset.mem_filter, Finset.mem_univ, true_and] at hrel'
        rcases hrel' with ⟨_, _, _, hcases⟩
        refine ⟨hColorableAdd, ?_⟩
        intro σ hσ
        have hc := (coloring_addPair_iff G u y e he σ).1 hσ
        rcases hcases σ hc.1 with hUy | hUv
        · exact (hc.2 hUy).elim
        · exact hUv
  refine ⟨hColorableAdd, ?_⟩
  apply Finset.ext
  intro v
  simp only [Finset.mem_union, frozenClass, Finset.mem_filter,
    Finset.mem_univ, true_and, relationSection, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hfreezeIff v

end ThLean.W.S609

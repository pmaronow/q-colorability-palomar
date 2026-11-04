module

public import ThLean.BP.SA.Interpolation

@[expose] public section

noncomputable section

namespace ThLean.W.SA33

open ThresholdFoundations

private lemma isColoring_addEdge_iff {V : Type*} (q : ℕ) (G : MGraph V)
    (x y : V) (σ : V → Fin q) :
    IsColoring q (addEdge G s(x, y)) σ ↔ IsColoring q G σ ∧ σ x ≠ σ y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v huv
      apply h u v
      by_cases heq : s(x, y) = s(u, v)
      · simp [addEdge, heq.symm]
      · have hne : s(u, v) ≠ s(x, y) := fun h => heq h.symm
        simpa [addEdge, hne] using huv
    · apply h x y
      simp [addEdge]
  · rintro ⟨hG, hxy⟩
    intro u v huv
    by_cases heq : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.mp heq with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
      · subst u
        subst v
        exact hxy
      · subst v
        subst u
        exact hxy.symm
    · apply hG u v
      have hne : s(u, v) ≠ s(x, y) := fun h => heq h.symm
      simpa [addEdge, hne] using huv

private lemma frozen_equivalence {V : Type*} [Fintype V] (q : ℕ)
    (G : MGraph V) (hG : Colorable q G) : Equivalence (Frozen q G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨hG, fun σ hσ => rfl⟩
  · intro x y hxy
    exact ⟨hG, fun σ hσ => (hxy.2 σ hσ).symm⟩
  · intro x y z hxy hyz
    exact ⟨hG, fun σ hσ => (hxy.2 σ hσ).trans (hyz.2 σ hσ)⟩

theorem SA_I14aStatement_holds : ThLean.BP.SA.SA_I14aStatement := by
  classical
  intro V _ q G hq hG
  refine ⟨frozen_equivalence q G hG, ?_, ?_⟩
  · intro v
    rcases hG with ⟨σ, hσ⟩
    by_contra hne
    have hpos : 0 < G (s(v, v)) := Nat.pos_of_ne_zero hne
    exact (hσ v v hpos) rfl
  · intro x y
    constructor
    · intro hfail
      refine ⟨hG, ?_⟩
      intro σ hσ
      by_contra hneq
      apply hfail
      exact ⟨σ, (isColoring_addEdge_iff q G x y σ).2 ⟨hσ, hneq⟩⟩
    · rintro ⟨_, hfreeze⟩ hcolorable
      rcases hcolorable with ⟨σ, hσ⟩
      have hparts := (isColoring_addEdge_iff q G x y σ).1 hσ
      exact hparts.2 (hfreeze σ hparts.1)

end ThLean.W.SA33

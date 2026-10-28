import ThLean.BP.S4.Reduction

noncomputable section
open scoped BigOperators

namespace ThLean.W.S441

open ThresholdFoundations

private def lowAt {V : Type*} [Fintype V] (G : MGraph V) (D : ℕ)
    (e : Sym2 V) : Prop :=
  ∃ u, Touches u e ∧ degree G u ≤ D

private def bothHighAt {V : Type*} [Fintype V] (G : MGraph V) (D : ℕ)
    (e : Sym2 V) : Prop :=
  ∀ u, Touches u e → D < degree G u

private def highAt {V : Type*} [Fintype V] (G : MGraph V) (D : ℕ)
    (e : Sym2 V) : Prop :=
  ∃ u, Touches u e ∧ D < degree G u

private theorem touches_mk_iff {V : Type*} (x u v : V) :
    Touches x (s(u, v)) ↔ x = u ∨ x = v := by
  simp only [Touches]
  constructor
  · rintro ⟨w, hw⟩
    rcases Sym2.eq_iff.mp hw with ⟨hxu, _⟩ | ⟨_, hvx⟩
    · exact Or.inl hxu.symm
    · exact Or.inr hvx.symm
  · rintro (h | h)
    · subst x
      exact ⟨v, by simp⟩
    · subst x
      exact ⟨u, by simp⟩

private theorem raw_split {V : Type*} [Fintype V] (G : MGraph V) (D : ℕ)
    (e : Sym2 V) :
    (lowAt G D e ↔ ¬ bothHighAt G D e) ∧
      (bothHighAt G D e → highAt G D e) := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      simp [lowAt, bothHighAt, highAt, touches_mk_iff]
      omega

private theorem raw_endpoints {V : Type*} [Fintype V] (G : MGraph V) (D : ℕ)
    (e : Sym2 V) (u v : V) (h : e = s(u, v)) :
    (lowAt G D e ↔ min (degree G u) (degree G v) ≤ D) ∧
      (bothHighAt G D e ↔ D < min (degree G u) (degree G v)) ∧
      (highAt G D e ↔ D < max (degree G u) (degree G v)) := by
  rw [h]
  simp [lowAt, bothHighAt, highAt, touches_mk_iff]

/-- The degree split is the endpoint partition used in prop:red-split. -/
theorem S4_RED_16Statement_holds : ThLean.BP.S4.S4_RED_16Statement := by
  classical
  intro V hV G e D
  have hs := raw_split G D e.val
  have he := raw_endpoints G D e.val
  simpa [lowEdge, bothHigh, highEdge, lowAt, bothHighAt, highAt] using
    (show (lowAt G D e.val ↔ ¬ bothHighAt G D e.val) ∧
        (bothHighAt G D e.val → highAt G D e.val) ∧
        (∀ u v : V, e.val = s(u, v) →
          (lowAt G D e.val ↔ min (degree G u) (degree G v) ≤ D) ∧
          (bothHighAt G D e.val ↔ D < min (degree G u) (degree G v)) ∧
          (highAt G D e.val ↔ D < max (degree G u) (degree G v))) from by
      refine ⟨hs.1, hs.2, ?_⟩
      intro u v h
      exact raw_endpoints G D e.val u v h)

example : ThLean.BP.S4.S4_RED_16Statement := S4_RED_16Statement_holds

end ThLean.W.S441

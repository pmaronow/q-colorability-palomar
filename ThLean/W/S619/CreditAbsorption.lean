import ThLean.BP.S6.Credit

noncomputable section

open ThresholdFoundations
open ThLean.BP.S6

namespace ThLean.W.S619

private theorem coloring_addPair_restrict {n q : ℕ} (G : Graph n) (e : Edge n)
    (σ : Fin n → Fin q) (hσ : IsColoring q (addPair G e) σ) : IsColoring q G σ := by
  intro x y hxy
  by_cases he : s(x, y) = e.val
  · have hnew : 0 < addPair G e (s(x, y)) := by
      unfold addPair addEdge
      rw [show s(x, y) = e.val from he]
      simp
    exact hσ x y hnew
  · have hnew : 0 < addPair G e (s(x, y)) := by
      simpa [addPair, addEdge, he] using hxy
    exact hσ x y hnew

private theorem section_mem_relation {n q : ℕ} (G : Graph n) (u x y : Fin n)
    (hy : y ∈ relationSection q G u x) : (x, y) ∈ relation q G u := by
  simpa [relationSection] using hy

private theorem credited_absorption_data {n q : ℕ}
    (G : Graph n) (u : Fin n) (e : Edge n) (hG : Colorable q G)
    (hnew : Colorable q (addPair G e)) (z : Fin n)
    (hz : z ∈ credited q G u e) :
    ¬ Frozen q G u z ∧ Frozen q (addPair G e) u z := by
  classical
  simp only [credited, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  rcases hz with ⟨a, b, hab, haz⟩
  by_cases ha : Frozen q G u a <;> by_cases hb : Frozen q G u b
  · simp [creditedAt, hG, ha, hb] at haz
  · have hsec : z ∈ relationSection q G u b := by
      simpa [creditedAt, hG, ha, hb] using haz
    have hrel := section_mem_relation G u b z hsec
    rcases (show Colorable q G ∧ ¬ Frozen q G u b ∧ ¬ Frozen q G u z ∧
        (∀ σ, IsColoring q G σ → (σ u = σ b ∨ σ u = σ z)) by
      simpa [relation] using hrel) with ⟨_, _, hznot, hrelAll⟩
    refine ⟨hznot, ?_⟩
    refine ⟨hnew, ?_⟩
    intro σ hσ
    have hσG := coloring_addPair_restrict G e σ hσ
    by_contra hune
    have hrootA : σ u = σ a := ha.2 σ hσG
    have hrootB : σ u = σ b := (hrelAll σ hσG).resolve_right hune
    have habColor : σ a = σ b := hrootA.symm.trans hrootB
    have hePos : 0 < addPair G e e.val := by
      simp [addPair, addEdge]
    have habPos : 0 < addPair G e (s(a, b)) := by
      rw [← hab]
      exact hePos
    exact (hσ a b habPos) habColor
  · have hsec : z ∈ relationSection q G u a := by
      simpa [creditedAt, hG, ha, hb] using haz
    have hrel := section_mem_relation G u a z hsec
    rcases (show Colorable q G ∧ ¬ Frozen q G u a ∧ ¬ Frozen q G u z ∧
        (∀ σ, IsColoring q G σ → (σ u = σ a ∨ σ u = σ z)) by
      simpa [relation] using hrel) with ⟨_, _, hznot, hrelAll⟩
    refine ⟨hznot, ?_⟩
    refine ⟨hnew, ?_⟩
    intro σ hσ
    have hσG := coloring_addPair_restrict G e σ hσ
    by_contra hune
    have hrootB : σ u = σ b := hb.2 σ hσG
    have hrootA : σ u = σ a := (hrelAll σ hσG).resolve_right hune
    have habColor : σ a = σ b := hrootA.symm.trans hrootB
    have hePos : 0 < addPair G e e.val := by
      simp [addPair, addEdge]
    have habPos : 0 < addPair G e (s(a, b)) := by
      rw [← hab]
      exact hePos
    exact (hσ a b habPos) habColor
  · have hsections : z ∈ relationSection q G u a ∧
        z ∈ relationSection q G u b := by
      simpa [creditedAt, hG, ha, hb] using haz
    have hrelA := section_mem_relation G u a z hsections.1
    have hrelB := section_mem_relation G u b z hsections.2
    rcases (show Colorable q G ∧ ¬ Frozen q G u a ∧ ¬ Frozen q G u z ∧
        (∀ σ, IsColoring q G σ → (σ u = σ a ∨ σ u = σ z)) by
      simpa [relation] using hrelA) with ⟨_, _, hznot, hallA⟩
    rcases (show Colorable q G ∧ ¬ Frozen q G u b ∧ ¬ Frozen q G u z ∧
        (∀ σ, IsColoring q G σ → (σ u = σ b ∨ σ u = σ z)) by
      simpa [relation] using hrelB) with ⟨_, _, _, hallB⟩
    refine ⟨hznot, ?_⟩
    refine ⟨hnew, ?_⟩
    intro σ hσ
    have hσG := coloring_addPair_restrict G e σ hσ
    by_contra hune
    have hrootA : σ u = σ a := (hallA σ hσG).resolve_right hune
    have hrootB : σ u = σ b := (hallB σ hσG).resolve_right hune
    have habColor : σ a = σ b := hrootA.symm.trans hrootB
    have hePos : 0 < addPair G e e.val := by
      simp [addPair, addEdge]
    have habPos : 0 < addPair G e (s(a, b)) := by
      rw [← hab]
      exact hePos
    exact (hσ a b habPos) habColor

theorem S6_18Statement_holds : ThLean.BP.S6.S6_18Statement := by
  classical
  intro n q hn hq G u e hG hnew
  let A := frozenClass q G u
  let B := credited q G u e
  let C := frozenClass q (addPair G e) u
  have hdata : ∀ z, z ∈ B → ¬ Frozen q G u z ∧ Frozen q (addPair G e) u z := by
    intro z hz
    exact credited_absorption_data G u e hG hnew z hz
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    have hza : Frozen q G u z := by
      simpa [A, frozenClass] using hzA
    exact (hdata z hzB).1 hza
  have hAsub : A ⊆ C := by
    intro z hz
    have hza : Frozen q G u z := by
      simpa [A, frozenClass] using hz
    have hzn : Frozen q (addPair G e) u z := by
      refine ⟨hnew, ?_⟩
      intro σ hσ
      exact hza.2 σ (coloring_addPair_restrict G e σ hσ)
    simpa [C, frozenClass] using hzn
  have hBsub : B ⊆ C := by
    intro z hz
    have hzb := (hdata z hz).2
    simpa [C, frozenClass] using hzb
  have hUnion : A ∪ B ⊆ C := Finset.union_subset hAsub hBsub
  have hcard : A.card + B.card ≤ C.card := by
    calc
      A.card + B.card = (A ∪ B).card := by
        rw [Finset.card_union_of_disjoint hdisj]
      _ ≤ C.card := Finset.card_le_card hUnion
  exact ⟨hdisj, hAsub, hBsub, hcard⟩

end ThLean.W.S619

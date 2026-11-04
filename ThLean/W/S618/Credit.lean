module

public import ThLean.BP.S6.Credit

@[expose] public section

noncomputable section
open ThresholdFoundations
attribute [local instance 10000] Fintype.decidableExistsFintype

namespace ThLean.W.S618

private theorem relationSection_subset_compl {V : Type} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : MGraph V) (u a : V) :
    ∀ v, v ∈ relationSection q G u a → ¬ Frozen q G u v := by
  intro v hv hfv
  have hrel : (a, v) ∈ relation q G u := by
    simpa [relationSection] using hv
  have hparts : Colorable q G ∧ ¬ Frozen q G u a ∧ ¬ Frozen q G u v ∧
      (∀ σ, IsColoring q G σ → (σ u = σ a ∨ σ u = σ v)) := by
    simpa [relation] using hrel
  exact hparts.2.2.1 hfv

private theorem creditedAt_not_frozen {n q : ℕ} (G : ThLean.BP.S6.Graph n)
    (u a b v : Fin n) (hv : v ∈ creditedAt q G u a b) :
    ¬ Frozen q G u v := by
  classical
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  by_cases hc : Colorable q G
  · by_cases ha : Frozen q G u a
    · by_cases hb : Frozen q G u b
      · simp [creditedAt, hc, ha, hb] at hv
      · exact relationSection_subset_compl q G u b v (by
          simpa [creditedAt, hc, ha, hb] using hv)
    · by_cases hb : Frozen q G u b
      · exact relationSection_subset_compl q G u a v (by
          simpa [creditedAt, hc, ha, hb] using hv)
      · apply relationSection_subset_compl q G u a v
        have hv' : v ∈ relationSection q G u a ∩ relationSection q G u b := by
          simpa [creditedAt, hc, ha, hb] using hv
        exact (Finset.mem_inter.mp hv').1
  · simp [creditedAt, hc] at hv

theorem S6_17Statement_holds : ThLean.BP.S6.S6_17Statement := by
  classical
  intro n q hn hq G u
  letI : DecidableEq (Fin n) := instDecidableEqFin n
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    letI : DecidableEq (Fin n) := fun x y => Classical.propDecidable (x = y)
    by_cases hcolor : Colorable q G
    · by_cases ha : Frozen q G u a <;>
      by_cases hb : Frozen q G u b <;>
      simp [creditedAt, hcolor, ha, hb, Finset.inter_comm]
    · simp [creditedAt, hcolor]
  · intro e
    have hsub : credited q G u e ⊆ Finset.univ \ frozenClass q G u := by
      intro v hv
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      letI : DecidableEq (Fin n) := fun x y => Classical.propDecidable (x = y)
      rcases Finset.mem_filter.mp hv with ⟨_, ⟨a, b, _, hcredit⟩⟩
      have hnot := creditedAt_not_frozen G u a b v hcredit
      simpa [frozenClass] using hnot
    refine ⟨hsub, ?_⟩
    have hdisj : Disjoint (frozenClass q G u) (credited q G u e) := by
      rw [Finset.disjoint_left]
      intro v hvC hvA
      have hvout := hsub hvA
      exact (Finset.mem_sdiff.mp hvout).2 hvC
    have hunion : frozenClass q G u ∪ credited q G u e ⊆ Finset.univ := by
      intro v _
      simp
    have hbound := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdisj] at hbound
    simpa using hbound
  · intro y e hcolor hy hEdge
    letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    have hfu : Frozen q G u u := ⟨hcolor, by intro σ hσ; rfl⟩
    have hyFrozen : ¬ Frozen q G u y := by
      intro hfy
      apply hy
      simp [frozenClass, hfy]
    have hAt₁ : creditedAt q G u u y = relationSection q G u y := by
      simp [creditedAt, hcolor, hfu, hyFrozen]
    have hAt₂ : creditedAt q G u y u = relationSection q G u y := by
      simp [creditedAt, hcolor, hfu, hyFrozen]
    apply Finset.ext
    intro v
    constructor
    · intro hv
      rcases (Finset.mem_filter.mp hv).2 with ⟨a, b, hab, hmem⟩
      have hend : s(a, b) = s(u, y) := hab.symm.trans hEdge
      rcases (Sym2.eq_iff.mp hend) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [hAt₁] using hmem
      · simpa [hAt₂] using hmem
    · intro hv
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨u, y, hEdge, by simpa [hAt₁] using hv⟩

end ThLean.W.S618

import ThLean.BP.S6.Deletion

noncomputable section
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S615

private theorem coloring_of_addPair {n q : ℕ} (G : ThLean.BP.S6.Graph n)
    (e : ThLean.BP.S6.Edge n) {σ : Fin n → Fin q}
    (hσ : IsColoring q (addPair G e) σ) : IsColoring q G σ := by
  letI : DecidableEq (Fin n) := fun x y => Classical.propDecidable (x = y)
  intro u v huv
  apply hσ u v
  have hle : G (s(u, v)) ≤ addPair G e (s(u, v)) := by
    unfold addPair addEdge
    change G (s(u, v)) ≤ Function.update G e.val (G e.val + 1) (s(u, v))
    simp only [Function.update]
    split_ifs with h
    · simp [h]
    · rfl
  exact lt_of_lt_of_le huv hle

private theorem addPair_edge_pos {n : ℕ} (G : ThLean.BP.S6.Graph n)
    (e : ThLean.BP.S6.Edge n) (a y : Fin n)
    (he : e.val = s(a, y)) : 0 < addPair G e (s(a, y)) := by
  letI : DecidableEq (Fin n) := fun x y => Classical.propDecidable (x = y)
  unfold addPair addEdge
  change 0 < Function.update G e.val (G e.val + 1) (s(a, y))
  rw [← he]
  simp [Function.update]

private theorem relationSection_not_frozen {n q : ℕ} (G : ThLean.BP.S6.Graph n)
    (a y v : Fin n) (hv : v ∈ relationSection q G a y) : ¬ Frozen q G a v := by
  letI : DecidableEq (Fin n) := fun x y => Classical.propDecidable (x = y)
  letI : DecidableEq (Fin n × Fin n) :=
    @instDecidableEqProd (Fin n) (Fin n)
      (fun x y => Classical.propDecidable (x = y))
      (fun x y => Classical.propDecidable (x = y))
  unfold relationSection at hv
  have hrel : (y, v) ∈ relation q G a := (Finset.mem_filter.mp hv).2
  rcases Finset.mem_filter.mp hrel with ⟨_, hprop⟩
  exact hprop.2.2.1

private theorem relationSection_empty_of_frozen {n q : ℕ} (G : ThLean.BP.S6.Graph n)
    (a y : Fin n) (hy : y ∈ frozenClass q G a) : relationSection q G a y = ∅ := by
  letI : DecidableEq (Fin n) := fun x y => Classical.propDecidable (x = y)
  letI : DecidableEq (Fin n × Fin n) :=
    @instDecidableEqProd (Fin n) (Fin n)
      (fun x y => Classical.propDecidable (x = y))
      (fun x y => Classical.propDecidable (x = y))
  unfold relationSection
  apply Finset.filter_false_of_mem
  intro v _ hrel
  rcases Finset.mem_filter.mp hrel with ⟨_, hprop⟩
  exact hprop.2.1 ((Finset.mem_filter.mp hy).2)

private theorem relationSection_empty_of_not_colorable {n q : ℕ}
    (G : ThLean.BP.S6.Graph n) (a y : Fin n) (hcol : ¬ Colorable q G) :
    relationSection q G a y = ∅ := by
  letI : DecidableEq (Fin n) := fun x y => Classical.propDecidable (x = y)
  letI : DecidableEq (Fin n × Fin n) :=
    @instDecidableEqProd (Fin n) (Fin n)
      (fun x y => Classical.propDecidable (x = y))
      (fun x y => Classical.propDecidable (x = y))
  unfold relationSection
  apply Finset.filter_false_of_mem
  intro v _ hrel
  rcases Finset.mem_filter.mp hrel with ⟨_, hprop⟩
  exact hcol hprop.1

theorem S6_13Statement_of_deps (h06 : ThLean.BP.S6.S6_06Statement) :
    ThLean.BP.S6.S6_13Statement := by
  intro n q hn hq G a y e hay he
  letI : DecidableEq (Fin n) := fun x y => Classical.propDecidable (x = y)
  letI : DecidableEq (Fin n × Fin n) :=
    @instDecidableEqProd (Fin n) (Fin n)
      (fun x y => Classical.propDecidable (x = y))
      (fun x y => Classical.propDecidable (x = y))
  by_cases hcol : Colorable q G
  · by_cases hy : y ∈ frozenClass q G a
    · have hsec : relationSection q G a y = ∅ :=
        relationSection_empty_of_frozen G a y hy
      have hnoadd : ¬ Colorable q (addPair G e) := by
        intro hnew
        rcases hnew with ⟨σ, hσ⟩
        have hσG : IsColoring q G σ := coloring_of_addPair G e hσ
        have hold : Frozen q G a y := (Finset.mem_filter.mp hy).2
        have heq : σ a = σ y := hold.2 σ hσG
        have hne : σ a ≠ σ y := hσ a y (addPair_edge_pos G e a y he)
        exact hne heq
      apply congrArg Finset.card
      rw [hsec]
      apply Finset.ext
      intro v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hnew, _⟩
        exact False.elim (hnoadd hnew.1)
      · intro hfalse
        exact False.elim ((Finset.notMem_empty v) hfalse)
    · have haddClass := (h06 n q hn hq G a y hcol hy).2 e he
      have haddColorable : Colorable q (addPair G e) := haddClass.1
      have hclass : frozenClass q (addPair G e) a =
          frozenClass q G a ∪ relationSection q G a y := by
        apply Finset.ext
        intro v
        have hmem := congrArg (fun S : Finset (Fin n) => v ∈ S) haddClass.2
        simpa only [Finset.mem_union] using Iff.of_eq hmem
      have haa : Frozen q G a a := ⟨hcol, fun _ _ => rfl⟩
      apply congrArg Finset.card
      apply Finset.ext
      intro v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hav, hnew, holdNot⟩
        have hvNew : v ∈ frozenClass q (addPair G e) a :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩
        rw [hclass] at hvNew
        rcases Finset.mem_union.mp hvNew with hOld | hSection
        · exact False.elim (holdNot ((Finset.mem_filter.mp hOld).2))
        · exact hSection
      · intro hSection
        have hnotOld : ¬ Frozen q G a v := by
          exact relationSection_not_frozen G a y v hSection
        have hvNew : v ∈ frozenClass q (addPair G e) a := by
          rw [hclass]
          exact Finset.mem_union.mpr (Or.inr hSection)
        have hnew : Frozen q (addPair G e) a v := (Finset.mem_filter.mp hvNew).2
        have hav : a ≠ v := by
          intro hav
          subst v
          exact hnotOld haa
        exact ⟨hav, hnew, hnotOld⟩
  · have hsec : relationSection q G a y = ∅ :=
      relationSection_empty_of_not_colorable G a y hcol
    apply congrArg Finset.card
    rw [hsec]
    apply Finset.ext
    intro v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hnew, _⟩
      rcases hnew.1 with ⟨σ, hσ⟩
      exact False.elim (hcol ⟨σ, coloring_of_addPair G e hσ⟩)
    · intro hfalse
      exact False.elim ((Finset.notMem_empty v) hfalse)

example (h06 : ThLean.BP.S6.S6_06Statement) :
    ThLean.BP.S6.S6_13Statement := S6_13Statement_of_deps h06

end ThLean.W.S615

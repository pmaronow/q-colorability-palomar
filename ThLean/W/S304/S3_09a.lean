import ThLean.BP.S3.Graph

noncomputable section

open ThresholdFoundations

namespace ThLean.W.S304

universe u

private theorem frozenClass_mem_iff {V : Type u} [Fintype V]
    (q : ℕ) (G : MGraph V) (a x : V) :
    x ∈ frozenClass q G a ↔ Frozen q G a x := by
  simp [frozenClass]

private theorem frozenClass_eq_of_frozen {V : Type u} [Fintype V]
    (q : ℕ) (G : MGraph V) (hcolorable : Colorable q G) {a b : V}
    (hab : Frozen q G a b) :
    frozenClass q G a = frozenClass q G b := by
  ext x
  rw [frozenClass_mem_iff, frozenClass_mem_iff]
  constructor
  · intro hax
    refine ⟨hcolorable, ?_⟩
    intro σ hσ
    exact (hab.2 σ hσ).symm.trans (hax.2 σ hσ)
  · intro hbx
    refine ⟨hcolorable, ?_⟩
    intro σ hσ
    exact (hab.2 σ hσ).trans (hbx.2 σ hσ)

private theorem frozenClass_disjoint_of_not_frozen {V : Type u} [Fintype V]
    (q : ℕ) (G : MGraph V) (hcolorable : Colorable q G) {a b : V}
    (hab : ¬ Frozen q G a b) :
    Disjoint (frozenClass q G a) (frozenClass q G b) := by
  apply Finset.disjoint_left.mpr
  intro x hax hbx
  apply hab
  refine ⟨hcolorable, ?_⟩
  intro σ hσ
  have hax' : Frozen q G a x := (frozenClass_mem_iff q G a x).mp hax
  have hbx' : Frozen q G b x := (frozenClass_mem_iff q G b x).mp hbx
  exact (hax'.2 σ hσ).trans (hbx'.2 σ hσ).symm

theorem S3_09aStatement_holds : ThLean.BP.S3.S3_09aStatement := by
  classical
  intro V _ q hq G hcolorable
  have hEquiv : Equivalence (Frozen q G) := {
    refl := by
      intro a
      refine ⟨hcolorable, ?_⟩
      intro σ hσ
      rfl
    symm := by
      intro a b hab
      refine ⟨hcolorable, ?_⟩
      intro σ hσ
      exact (hab.2 σ hσ).symm
    trans := by
      intro a b c hab hbc
      refine ⟨hcolorable, ?_⟩
      intro σ hσ
      exact (hab.2 σ hσ).trans (hbc.2 σ hσ)
  }
  refine ⟨hEquiv, ?_, ?_, ?_, ?_⟩
  · intro a
    simp [frozenClass, Frozen, hcolorable]
  · intro C hC
    simp only [frozenClasses, Finset.mem_filter] at hC
    exact hC.2
  · intro C hC D hD
    simp only [frozenClasses, Finset.mem_filter] at hC hD
    rcases Finset.mem_image.mp hC.1 with ⟨a, _, ha⟩
    rcases Finset.mem_image.mp hD.1 with ⟨b, _, hb⟩
    by_cases hab : Frozen q G a b
    · left
      calc
        C = frozenClass q G a := ha.symm
        _ = frozenClass q G b := frozenClass_eq_of_frozen q G hcolorable hab
        _ = D := hb
    · right
      rw [← ha, ← hb]
      exact frozenClass_disjoint_of_not_frozen q G hcolorable hab
  · intro a
    refine ⟨frozenClass q G a, ?_, ?_⟩
    · simp only [frozenClasses, Finset.mem_filter]
      constructor
      · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
      · exact ⟨a, by
          simp [frozenClass, Frozen, hcolorable]⟩
    · simp [frozenClass, Frozen, hcolorable]

end ThLean.W.S304

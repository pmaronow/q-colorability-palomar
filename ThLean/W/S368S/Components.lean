module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
universe u
namespace ThLean.W.S368S
open ThresholdFoundations ThLean.BP.S3

variable {V : Type u} [Fintype V]

noncomputable instance componentFintype (G : MGraph V)
    (C : (graphSupport G).ConnectedComponent) : Fintype C := Fintype.ofFinite C

def componentGraph (G : MGraph V) (C : (graphSupport G).ConnectedComponent) :
    MGraph C := fun e => G (Sym2.map Subtype.val e)

lemma componentGraph_loopless (G : MGraph V) (hG : Loopless G)
    (C : (graphSupport G).ConnectedComponent) : Loopless (componentGraph G C) := by
  intro a
  exact hG a.val

lemma componentGraph_connected (G : MGraph V)
    (C : (graphSupport G).ConnectedComponent) :
    (graphSupport (componentGraph G C)).Connected := by
  classical
  have heq : graphSupport (componentGraph G C) = C.toSimpleGraph := by
    ext a b
    change (a ≠ b ∧ 0 < G s(a.val, b.val)) ↔
      (a.val ≠ b.val ∧ 0 < G s(a.val, b.val))
    simp only [Ne, Subtype.ext_iff]
  rw [heq]
  exact C.connected_toSimpleGraph

lemma colorable_of_components (q : ℕ) (G : MGraph V) (hG : Loopless G)
    (h : ∀ C : (graphSupport G).ConnectedComponent, Colorable q (componentGraph G C)) :
    Colorable q G := by
  classical
  let τ : ∀ C : (graphSupport G).ConnectedComponent, C → Fin q :=
    fun C => Classical.choose (h C)
  have hτ : ∀ C, IsColoring q (componentGraph G C) (τ C) :=
    fun C => Classical.choose_spec (h C)
  refine ⟨fun a => τ ((graphSupport G).connectedComponentMk a)
    ⟨a, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩, ?_⟩
  intro a b hab
  have hne : a ≠ b := by
    rintro rfl
    simp [hG a] at hab
  have heq : (graphSupport G).connectedComponentMk a =
      (graphSupport G).connectedComponentMk b :=
    SimpleGraph.ConnectedComponent.sound
      (show (graphSupport G).Adj a b from ⟨hne, hab⟩).reachable
  change τ ((graphSupport G).connectedComponentMk a) _ ≠
    τ ((graphSupport G).connectedComponentMk b) _
  have aux : ∀ (C D : (graphSupport G).ConnectedComponent), C = D →
      ∀ (ha : a ∈ C) (hb : b ∈ D), τ C ⟨a, ha⟩ ≠ τ D ⟨b, hb⟩ := by
    intro C D hCD ha hb
    subst D
    exact hτ C ⟨a, ha⟩ ⟨b, hb⟩ hab
  exact aux _ _ heq _ _

lemma card_ge_two_of_not_colorable (q : ℕ) (hq : 0 < q) (G : MGraph V)
    (hG : Loopless G) (hn : ¬ Colorable q G) : 2 ≤ Fintype.card V := by
  classical
  by_contra hcard
  have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  apply hn
  refine ⟨fun _ => ⟨0, hq⟩, ?_⟩
  intro a b hab
  have heq : a = b := Subsingleton.elim _ _
  subst b
  simp [hG a] at hab

lemma exists_bad_component (q : ℕ) (hq : 0 < q) (G : MGraph V)
    (hG : Loopless G) (hn : ¬ Colorable q G) :
    ∃ C : (graphSupport G).ConnectedComponent,
      2 ≤ Fintype.card C ∧ ¬ Colorable q (componentGraph G C) := by
  classical
  have hbad : ∃ C : (graphSupport G).ConnectedComponent,
      ¬ Colorable q (componentGraph G C) := by
    by_contra h
    push Not at h
    exact hn (colorable_of_components q G hG h)
  obtain ⟨C, hC⟩ := hbad
  exact ⟨C, card_ge_two_of_not_colorable q hq _ (componentGraph_loopless G hG C) hC, hC⟩

end ThLean.W.S368S

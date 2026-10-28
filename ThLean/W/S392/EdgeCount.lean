import ThLean.Contrib.S392.Nodes

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S392
open ThresholdFoundations

private theorem endpoints_supported {V : Type u} [Fintype V] (G : MGraph V)
    {e : Sym2 V} (he : 0 < G e) : ∀ v ∈ e, v ∈ vertexSupport G := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    intro v hv
    rcases (Sym2.mem_iff.mp hv) with hv | hv
    · subst v
      simp [vertexSupport]
      exact ⟨s(a,b), he, b, rfl⟩
    · subst v
      simp [vertexSupport]
      exact ⟨s(a,b), he, a, by rw [Sym2.eq_swap]⟩

private theorem sum_eq_sum_positive {α : Type u} [Fintype α] (f : α → ℕ) :
    (∑ x, f x) = ∑ x ∈ Finset.univ.filter (fun x => 0 < f x), f x := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun x => 0 < f x) (f := f)]
  have hz : ∑ x ∈ Finset.univ.filter (fun x => ¬ 0 < f x), f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx' : ¬ 0 < f x := (Finset.mem_filter.mp hx).2
    omega
  rw [hz, add_zero]

private def positiveEdgeMap (V : Type u) [Fintype V] (G : MGraph V) :
    {e : Sym2 {v : V // v ∈ vertexSupport G} //
      0 < G (Sym2.map Subtype.val e)} → {e : Sym2 V // 0 < G e} :=
  fun e => ⟨Sym2.map Subtype.val e.1, by simpa [inducedGraph] using e.2⟩

private theorem positiveEdgeMap_bijective (V : Type u) [Fintype V] (G : MGraph V) :
    Function.Bijective (positiveEdgeMap V G) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    exact congrArg Subtype.val h
  · rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hp : 0 < G (s(a,b)) := he
      have ha : a ∈ vertexSupport G := endpoints_supported G hp a (by simp)
      have hb : b ∈ vertexSupport G := endpoints_supported G hp b (by simp)
      refine ⟨⟨s(⟨a,ha⟩,⟨b,hb⟩), ?_⟩, ?_⟩
      · change 0 < G (Sym2.map Subtype.val (s(⟨a,ha⟩,⟨b,hb⟩)))
        simpa [Sym2.map_mk] using hp
      · apply Subtype.ext
        simp [positiveEdgeMap, Sym2.map_mk]

theorem S3_57bEdgeCount_proved {V : Type u} [Fintype V] (G : MGraph V) :
    edgeCount (inducedGraph G (vertexSupport G)) = edgeCount G := by
  classical
  unfold edgeCount
  rw [sum_eq_sum_positive, sum_eq_sum_positive]
  rw [← Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
    (p := fun e : Sym2 {v : V // v ∈ vertexSupport G} =>
      0 < (inducedGraph G (vertexSupport G)) e)]
  rw [← Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
    (p := fun e : Sym2 V => 0 < G e)]
  simp only [Finset.subtype_univ]
  exact Fintype.sum_bijective (positiveEdgeMap V G) (positiveEdgeMap_bijective V G)
    _ _ (by intro e; rfl)

end ThLean.W.S392

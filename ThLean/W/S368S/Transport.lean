import ThLean.BP.S3.Cycles

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.W.S368S
open ThresholdFoundations ThLean.BP.S3

variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]

lemma mapGraph_add (f : V → W) (G H : MGraph V) :
    mapGraph f (G + H) = mapGraph f G + mapGraph f H := by
  classical
  funext e
  unfold mapGraph
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : Sym2.map f a = e <;> simp [h]

lemma mapGraph_single (f : V → W) (a : Sym2 V) :
    mapGraph f (fun e => if a = e then 1 else 0) =
      fun e => if Sym2.map f a = e then 1 else 0 := by
  classical
  funext e
  unfold mapGraph
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hb
    simp [Ne.symm hb]

lemma edgesGraph_cons (a : Sym2 V) (xs : List (Sym2 V)) :
    edgesGraph (a :: xs) = (fun e => if a = e then 1 else 0) + edgesGraph xs := by
  classical
  funext e
  by_cases h : a = e <;> simp [edgesGraph, h, Nat.add_comm]

lemma mapGraph_edgesGraph (f : V → W) (xs : List (Sym2 V)) :
    mapGraph f (edgesGraph xs) = edgesGraph (xs.map (Sym2.map f)) := by
  classical
  induction xs with
  | nil => funext e; simp [mapGraph, edgesGraph]
  | cons a xs ih =>
    simp only [List.map_cons, edgesGraph_cons, mapGraph_add, mapGraph_single, ih]

omit [Fintype V] [Fintype W] in
lemma consecutiveEdges_map (f : V → W) (xs : List V) :
    (consecutiveEdges xs).map (Sym2.map f) = consecutiveEdges (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs => simpa [consecutiveEdges] using congrArg (List.cons s(f a, f b)) ih

lemma mapGraph_thetaCode {k : ℕ} (hk : 0 < k) (j₁ j₂ j₃ : ℕ)
    (f : V → W) (labels : Fin k → V) :
    mapGraph f (thetaCode hk j₁ j₂ j₃ labels) =
      thetaCode hk j₁ j₂ j₃ (f ∘ labels) := by
  simp [thetaCode, mapGraph_edgesGraph, List.map_append, consecutiveEdges_map,
    List.map_map, codeLabel, Function.comp_def]

lemma mapGraph_dumbbellCode {k : ℕ} (hk : 0 < k) (j₁ j₂ j₃ : ℕ)
    (f : V → W) (labels : Fin k → V) :
    mapGraph f (dumbbellCode hk j₁ j₂ j₃ labels) =
      dumbbellCode hk j₁ j₂ j₃ (f ∘ labels) := by
  by_cases h : j₃ = 0 <;>
    simp [dumbbellCode, h, mapGraph_edgesGraph, List.map_append,
      consecutiveEdges_map, List.map_map, codeLabel, Function.comp_def] <;> rfl

lemma mapGraph_apply_map (f : V → W) (hf : Function.Injective f)
    (G : MGraph V) (e : Sym2 V) :
    mapGraph f G (Sym2.map f e) = G e := by
  classical
  unfold mapGraph
  simp only [(Sym2.map.injective hf).eq_iff]
  simp

lemma mapGraph_subgraph (f : V → W) (hf : Function.Injective f)
    (F : MGraph V) (G : MGraph W)
    (h : ∀ e, F e ≤ G (Sym2.map f e)) : subgraph (mapGraph f F) G := by
  classical
  intro e
  by_cases he : ∃ a, Sym2.map f a = e
  · obtain ⟨a, rfl⟩ := he
    rw [mapGraph_apply_map f hf]
    exact h a
  · have hz : mapGraph f F e = 0 := by
      unfold mapGraph
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (fun ha => he ⟨a, ha⟩)
    rw [hz]
    exact Nat.zero_le _

omit [Fintype V] in
lemma loopless_of_subgraph (F G : MGraph V) (h : subgraph F G)
    (hG : Loopless G) : Loopless F := by
  intro a
  exact Nat.eq_zero_of_le_zero (by simpa [hG a] using h s(a,a))

end ThLean.W.S368S

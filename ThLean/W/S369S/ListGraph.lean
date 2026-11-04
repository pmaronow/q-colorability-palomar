module

public import ThLean.W.S369.ThetaEncoding

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S369S
open ThresholdFoundations ThLean.BP.S3

variable {V : Type u} [Fintype V]

theorem card_get_fiber (xs : List (Sym2 V)) (e : Sym2 V) :
    Fintype.card {i : Fin xs.length // xs.get i = e} = edgesGraph xs e := by
  classical
  rw [Fintype.card_subtype]
  have hn := List.nodup_finRange xs.length
  have hu : (List.finRange xs.length).toFinset = Finset.univ := by ext; simp
  rw [← hu, hn.card_eq_countP]
  calc
    _ = List.countP (fun f => decide (f = e)) ((List.finRange xs.length).map xs.get) :=
      List.countP_map.symm
    _ = _ := by simp [edgesGraph, List.countP_eq_length_filter]

/-- The positions in an edge list are distinct occurrences, even for repeated pairs. -/
def listOccEquiv (xs : List (Sym2 V)) : Fin xs.length ≃ Occurrence (edgesGraph xs) :=
  (Equiv.sigmaFiberEquiv xs.get).symm.trans
    (Equiv.sigmaCongrRight fun e => Fintype.equivFinOfCardEq (card_get_fiber xs e))

@[simp] theorem listOccEquiv_pair (xs : List (Sym2 V)) (i : Fin xs.length) :
    (listOccEquiv xs i).1 = xs.get i := rfl

theorem graph_of_occurrence_list {G : MGraph V} (xs : List (Occurrence G))
    (hn : xs.Nodup) (hu : xs.toFinset = Finset.univ) :
    edgesGraph (xs.map Sigma.fst) = G := by
  funext e
  have hc := hn.card_eq_countP (P := fun o => o.1 = e)
  rw [hu] at hc
  calc
    edgesGraph (xs.map Sigma.fst) e = xs.countP (fun o => decide (o.1 = e)) := by
      simp [edgesGraph, List.filter_map, List.countP_eq_length_filter, Function.comp_def]
    _ = (Finset.univ.filter (fun o : Occurrence G => o.1 = e)).card := hc.symm
    _ = G e := by
      let E : {o : Occurrence G // o.1 = e} ≃ Fin (G e) := {
        toFun := fun ⟨⟨e', i⟩, h⟩ => h ▸ i
        invFun := fun i => ⟨⟨e, i⟩, rfl⟩
        left_inv := by rintro ⟨⟨e', i⟩, h⟩; change e' = e at h; subst e'; rfl
        right_inv := by intro i; rfl }
      rw [← Fintype.card_subtype]
      exact (Fintype.card_congr E).trans (Fintype.card_fin _)

theorem consecutiveEdges_ofFn {n : ℕ} (f : Fin (n+1) → V) :
    consecutiveEdges (List.ofFn f) =
      List.ofFn (fun i : Fin n => s(f i.castSucc, f i.succ)) := by
  apply List.ext_getElem
  · simp [consecutiveEdges, List.length_zip]
  · intro i hi hj
    simp only [consecutiveEdges, List.getElem_map, List.getElem_zip,
      List.getElem_tail, List.getElem_ofFn]
    rfl

def pathInterior {G : MGraph V} (p : OccurrencePath G) : List V :=
  List.ofFn (fun i : Fin (p.length - 1) => p.vertex ⟨i.val + 1, by omega⟩)

theorem path_list {G : MGraph V} (p : OccurrencePath G) (a b : V)
    (hp : 1 ≤ p.length) (hab : PathFrom p a b) :
    List.ofFn p.vertex = [a] ++ pathInterior p ++ [b] := by
  apply List.ext_getElem
  · simp [pathInterior]; omega
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn, List.getElem_append, List.length_append,
      List.length_singleton, pathInterior, List.length_ofFn]
    split_ifs with h1 h2
    · have : i = 0 := by omega
      subst i
      exact hab.1
    · have hh : i - 1 + 1 = i := by omega
      congr 1
      apply Fin.ext
      exact hh.symm
    · have hh : i - (1 + (p.length - 1)) = 0 := by omega
      have hl : i = p.length := by omega
      simp only [hh, List.getElem_cons_zero]
      subst i
      exact hab.2

theorem pathInterior_nodup {G : MGraph V} (p : OccurrencePath G) :
    (pathInterior p).Nodup := by
  rw [pathInterior, List.nodup_ofFn]
  intro i j hij
  have h := congrArg Fin.val (p.vertex_injective hij)
  apply Fin.ext
  dsimp at h
  omega

theorem mem_pathInterior {G : MGraph V} (p : OccurrencePath G) (x : V) :
    x ∈ pathInterior p ↔ ∃ i : Fin (p.length+1), 0 < i.val ∧ i.val < p.length ∧ p.vertex i = x := by
  simp only [pathInterior, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    refine ⟨⟨i.val+1, by omega⟩, ?_, ?_, rfl⟩ <;> dsimp <;> omega
  · rintro ⟨i, h0, hl, rfl⟩
    refine ⟨⟨i.val-1, by omega⟩, ?_⟩
    congr 1
    apply Fin.ext
    dsimp
    omega

theorem edgesGraph_append (xs ys : List (Sym2 V)) :
    edgesGraph (xs ++ ys) = fun e => edgesGraph xs e + edgesGraph ys e := by
  funext e
  simp [edgesGraph]

theorem mem_vertexSupport_edgesGraph (xs : List (Sym2 V)) (x : V) :
    x ∈ vertexSupport (edgesGraph xs) ↔ ∃ e ∈ xs, Touches x e := by
  simp only [vertexSupport, Finset.mem_filter, Finset.mem_univ, true_and, edgesGraph,
    List.length_pos_iff_exists_mem, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨f, hf, rfl⟩, ht⟩
    exact ⟨f, hf, ht⟩
  · rintro ⟨e, he, ht⟩
    exact ⟨e, ⟨e, he, rfl⟩, ht⟩

theorem consecutiveEdges_get (xs : List V) (i : ℕ) (hi : i+1 < xs.length) :
    (consecutiveEdges xs)[i]'(by simp [consecutiveEdges, List.length_zip]; omega) =
      s(xs[i], xs[i+1]) := by
  simp only [consecutiveEdges, List.getElem_map, List.getElem_zip, List.getElem_tail]

theorem mem_consecutiveEdges (xs : List V) (e : Sym2 V) :
    e ∈ consecutiveEdges xs ↔ ∃ (i : ℕ) (hi : i+1 < xs.length), e = s(xs[i],xs[i+1]) := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hb : i+1 < xs.length := by
      rw [ThLean.W.S369.consecutiveEdges_length] at hi
      omega
    exact ⟨i, hb, consecutiveEdges_get xs i hb⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [ThLean.W.S369.consecutiveEdges_length]; omega,
      consecutiveEdges_get xs i hi⟩

theorem support_consecutiveEdges (xs : List V) (hx : 2 ≤ xs.length) :
    vertexSupport (edgesGraph (consecutiveEdges xs)) = xs.toFinset := by
  ext x
  rw [mem_vertexSupport_edgesGraph]
  simp only [List.mem_toFinset]
  constructor
  · rintro ⟨e, he, y, hxy⟩
    obtain ⟨i, hi, rfl⟩ := (mem_consecutiveEdges xs e).mp he
    have hm : x ∈ s(xs[i],xs[i+1]) := by rw [hxy]; simp
    rcases Sym2.mem_iff.mp hm with h | h
    · exact h ▸ List.getElem_mem (by omega)
    · exact h ▸ List.getElem_mem hi
  · intro hm
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    by_cases hl : i+1 < xs.length
    · refine ⟨s(xs[i],xs[i+1]), (mem_consecutiveEdges xs _).mpr ⟨i, hl, rfl⟩, ?_⟩
      exact ⟨xs[i+1], rfl⟩
    · have hp : i-1+1 = i := by omega
      refine ⟨s(xs[i-1],xs[i]), (mem_consecutiveEdges xs _).mpr ?_, ?_⟩
      · exact ⟨i-1, by omega, by simp only [hp]⟩
      · exact ⟨xs[i-1], Sym2.eq_swap⟩

theorem support_append (xs ys : List (Sym2 V)) :
    vertexSupport (edgesGraph (xs ++ ys)) =
      vertexSupport (edgesGraph xs) ∪ vertexSupport (edgesGraph ys) := by
  ext x
  simp only [Finset.mem_union, mem_vertexSupport_edgesGraph, List.mem_append]
  aesop

end ThLean.W.S369S

module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3

variable {V : Type u} [Fintype V]

theorem edgesGraph_append (xs ys : List (Sym2 V)) :
    edgesGraph (xs ++ ys) = fun e => edgesGraph xs e + edgesGraph ys e := by
  classical
  funext e
  simp [edgesGraph]

theorem edgeCount_edgesGraph (xs : List (Sym2 V)) :
    edgeCount (edgesGraph xs) = xs.length := by
  classical
  induction xs with
  | nil => simp [edgeCount, edgesGraph]
  | cons x xs ih =>
    have he : edgesGraph (x :: xs) = fun e => edgesGraph xs e + if x = e then 1 else 0 := by
      funext e
      by_cases h : x = e <;> simp [edgesGraph, h]
    simp only [he, edgeCount, Finset.sum_add_distrib]
    change edgeCount (edgesGraph xs) + _ = _
    simp [ih]

omit [Fintype V] in
theorem consecutiveEdges_length (xs : List V) :
    (consecutiveEdges xs).length = xs.length - 1 := by
  simp [consecutiveEdges, List.length_zip, List.length_tail]

theorem dumbbellCode_edgeCount {k : ℕ} (hk : 0 < k)
    (j₁ j₂ j₃ : ℕ) (labels : Fin k → V)
    (hj₁ : 2 ≤ j₁) (hj₂ : 2 ≤ j₂) (hsum : j₁+j₂+j₃ = k+1) :
    edgeCount (dumbbellCode hk j₁ j₂ j₃ labels) = k+1 := by
  classical
  unfold dumbbellCode
  split <;> rw [edgeCount_edgesGraph] <;>
    simp only [List.length_append, consecutiveEdges_length, List.length_map,
      List.length_range, List.length_cons, List.length_nil] <;> omega

theorem edgesGraph_pos_iff (xs : List (Sym2 V)) (e : Sym2 V) :
    0 < edgesGraph xs e ↔ e ∈ xs := by
  classical
  simp [edgesGraph, List.length_pos_iff]

theorem mem_vertexSupport_edgesGraph (xs : List (Sym2 V)) (a : V) :
    a ∈ vertexSupport (edgesGraph xs) ↔ ∃ e ∈ xs, Touches a e := by
  classical
  simp [vertexSupport, edgesGraph_pos_iff]

omit [Fintype V] in
theorem consecutiveEdges_ofFn {n : ℕ} (v : Fin (n+1) → V) :
    consecutiveEdges (List.ofFn v) =
      List.ofFn (fun i : Fin n => s(v i.castSucc, v i.succ)) := by
  apply List.ext_getElem
  · simp [consecutiveEdges_length]
  · intro i hi hj
    simp only [consecutiveEdges, List.getElem_map, List.getElem_zip,
      List.getElem_tail, List.getElem_ofFn]
    rfl

theorem filter_length_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    (List.filter p (List.ofFn f)).length =
      (Finset.univ.filter (fun i => p (f i))).card := by
  rw [← List.countP_eq_length_filter]
  have hs : (List.ofFn f).countP p = ∑ i, if p (f i) then 1 else 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ, ih]
      split <;> simp_all [Nat.add_comm]
  rw [hs]
  simp

theorem fiber_card_ofFn {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (e : α) :
    Fintype.card {i : Fin n // f i = e} =
      (List.filter (fun x => x = e) (List.ofFn f)).length := by
  rw [filter_length_ofFn, Fintype.card_subtype]
  simp

def listOccurrenceEquiv (xs : List (Sym2 V)) :
    Fin xs.length ≃ Occurrence (edgesGraph xs) := by
  classical
  exact (Equiv.sigmaFiberEquiv xs.get).symm.trans
    (Equiv.sigmaCongrRight (fun e => Fintype.equivFinOfCardEq (by
      simpa [edgesGraph, List.ofFn_get] using fiber_card_ofFn xs.get e)))

@[simp] theorem listOccurrenceEquiv_pair (xs : List (Sym2 V)) (i : Fin xs.length) :
    (listOccurrenceEquiv xs i).1 = xs.get i := rfl

omit [Fintype V] in
theorem touches_pair (a x y : V) : Touches a (s(x,y)) ↔ a = x ∨ a = y := by
  constructor
  · rintro ⟨b, hb⟩
    rcases Sym2.eq_iff.mp hb with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact ⟨y, rfl⟩
    · exact ⟨x, Sym2.eq_swap⟩

theorem edgesGraph_occurrences {G : MGraph V} (xs : List (Occurrence G))
    (hnd : xs.Nodup) (hfull : xs.toFinset = Finset.univ) :
    edgesGraph (xs.map Sigma.fst) = G := by
  classical
  funext e
  change (List.filter (fun x => x = e) (xs.map Sigma.fst)).length = G e
  rw [← List.countP_eq_length_filter, List.countP_map, List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter, hfull]
  have h := Fintype.card_congr (Equiv.sigmaSubtype (β := fun e => Fin (G e)) e)
  simpa [Fintype.card_subtype] using h

omit [Fintype V] in
theorem consecutiveEdges_cycle {n : ℕ} (hn : 0 < n) (v : Fin n → V) :
    consecutiveEdges (List.ofFn v ++ [v ⟨0, hn⟩]) =
      List.ofFn (fun i : Fin n => s(v i, v ⟨(i.val+1)%n, Nat.mod_lt _ hn⟩)) := by
  apply List.ext_getElem
  · simp [consecutiveEdges_length]
  · intro i hi hj
    have hin : i < n := by simpa using hj
    simp only [consecutiveEdges, List.getElem_map, List.getElem_zip,
      List.getElem_tail, List.getElem_ofFn]
    rw [List.getElem_append_left (by simpa using hin), List.getElem_ofFn]
    by_cases hl : i+1 < n
    · rw [List.getElem_append_left (by simpa using hl), List.getElem_ofFn]
      simp [Nat.mod_eq_of_lt hl]
    · have he : i+1 = n := by omega
      rw [List.getElem_append_right (by simp; omega)]
      simp [he]

theorem cycle_edgeList {G : MGraph V} (c : OccurrenceCycle G) :
    (List.ofFn c.edge).map Sigma.fst =
      consecutiveEdges (List.ofFn c.vertex ++ [c.vertex ⟨0, by have := c.length_ge_two; omega⟩]) := by
  rw [List.map_ofFn, consecutiveEdges_cycle]
  · congr 1
    funext i
    exact c.joins i

theorem path_edgeList {G : MGraph V} (p : OccurrencePath G) :
    (List.ofFn p.edge).map Sigma.fst = consecutiveEdges (List.ofFn p.vertex) := by
  rw [List.map_ofFn, consecutiveEdges_ofFn]
  congr 1
  funext i
  exact p.joins i

end ThLean.W.S370S

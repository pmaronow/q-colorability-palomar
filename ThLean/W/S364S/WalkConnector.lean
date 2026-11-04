module

public import ThLean.W.S364.S3_61

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S364S

open ThresholdFoundations ThLean.BP.S3

variable {V : Type*}

/-- A shortest simple path between two disjoint, nonempty vertex sets can
meet the first set only at index zero and the second only at its last index. -/
theorem shortestPath_between {G : SimpleGraph V} (hG : G.Connected)
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) :
    ∃ (a b : V) (w : G.Walk a b), a ∈ A ∧ b ∈ B ∧ w.IsPath ∧
      1 ≤ w.length ∧
      (∀ i : ℕ, i ≤ w.length → w.getVert i ∈ A → i = 0) ∧
      (∀ i : ℕ, i ≤ w.length → w.getVert i ∈ B → i = w.length) := by
  classical
  have hex : ∃ n : ℕ, ∃ a ∈ A, ∃ b ∈ B, ∃ w : G.Walk a b,
      w.IsPath ∧ w.length = n := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    obtain ⟨w, hw⟩ := hG.exists_isPath a b
    exact ⟨w.length, a, ha, b, hb, w, hw, rfl⟩
  obtain ⟨a, ha, b, hb, w, hw, hlen⟩ := Nat.find_spec hex
  have hmin {x y : V} (hx : x ∈ A) (hy : y ∈ B)
      (z : G.Walk x y) (hz : z.IsPath) : w.length ≤ z.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨x, hx, y, hy, z, hz, rfl⟩
  have hpos : 1 ≤ w.length := by
    by_contra h
    have hz : w.length = 0 := by omega
    have hab : a = b := by simpa [hz] using w.getVert_length
    exact Finset.disjoint_left.mp hAB ha (hab ▸ hb)
  refine ⟨a, b, w, ha, hb, hw, hpos, ?_, ?_⟩
  · intro i hi hx
    have hle := hmin hx hb (w.drop i) (hw.drop i)
    rw [SimpleGraph.Walk.drop_length] at hle
    omega
  · intro i hi hy
    have hle := hmin ha hy (w.take i) (hw.take i)
    rw [SimpleGraph.Walk.take_length, Nat.min_eq_left hi] at hle
    omega

variable [Fintype V]

/-- Lift a simple support path by selecting occurrence zero of each edge.
Distinct edges of a simple path give distinct selected occurrences. -/
def occurrencePathOfWalk {K : MGraph V} {a b : V}
    (w : (graphSupport K).Walk a b) (hw : w.IsPath) : OccurrencePath K where
  length := w.length
  vertex := fun i => w.getVert i.val
  edge := fun i =>
    ⟨s(w.getVert i.val, w.getVert (i.val + 1)),
      ⟨0, (w.adj_getVert_succ i.isLt).2⟩⟩
  vertex_injective := by
    intro i j hij
    apply Fin.ext
    exact hw.getVert_injOn (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) hij
  edge_injective := by
    intro i j hij
    apply Fin.ext
    have hpair : s(w.getVert i.val, w.getVert (i.val + 1)) =
        s(w.getVert j.val, w.getVert (j.val + 1)) := congrArg Sigma.fst hij
    have hedge : w.edges[i.val] = w.edges[j.val] := by
      have hi : i.val < w.edges.length := by simp
      have hj : j.val < w.edges.length := by simp
      rw [w.getElem_edges hi, w.getElem_edges hj]
      exact hpair
    exact hw.edges_nodup.getElem_inj_iff.mp hedge
  joins := by intro i; rfl

theorem pathFrom_occurrencePathOfWalk {K : MGraph V} {a b : V}
    (w : (graphSupport K).Walk a b) (hw : w.IsPath) :
    PathFrom (occurrencePathOfWalk w hw) a b := by
  constructor <;> simp [occurrencePathOfWalk]

end ThLean.W.S364S

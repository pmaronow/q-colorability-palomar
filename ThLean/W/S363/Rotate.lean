import ThLean.BP.S3.Cycles

universe u

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S363
open ThresholdFoundations

def nextIndex {n : ℕ} [NeZero n] (i : Fin n) : Fin n := i + 1

theorem nextIndex_eq {n : ℕ} [NeZero n] (i : Fin n) :
    nextIndex i = ⟨(i.val + 1) % n,
      Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩ := by
  apply Fin.ext
  simp [nextIndex, Fin.add_def]

theorem finCycle_next {n : ℕ} [NeZero n] (s i : Fin n) :
    finCycle s (nextIndex i) = nextIndex (finCycle s i) := by
  change (i + 1) + s = (i + s) + 1
  ac_rfl

def rotateCycle {V : Type u} [Fintype V] {G : MGraph V}
    (c : OccurrenceCycle G) (s : Fin c.length) : OccurrenceCycle G :=
  {
    length := c.length
    length_ge_two := c.length_ge_two
    vertex := fun i => c.vertex (finCycle s i)
    edge := fun i => c.edge (finCycle s i)
    vertex_injective := c.vertex_injective.comp (finCycle s).injective
    edge_injective := c.edge_injective.comp (finCycle s).injective
    joins := by
      letI : NeZero c.length := ⟨by
        have hc := c.length_ge_two
        omega⟩
      intro i
      rw [c.joins (finCycle s i)]
      congr 2
      simpa [nextIndex, Fin.add_def] using (finCycle_next s i).symm }

@[simp] theorem rotateCycle_length {V : Type u} [Fintype V] {G : MGraph V}
    (c : OccurrenceCycle G) (s : Fin c.length) :
    (rotateCycle c s).length = c.length := rfl

theorem rotate_cycleVertices {V : Type u} [Fintype V] {G : MGraph V}
    (c : OccurrenceCycle G) (s : Fin c.length) :
    cycleVertices (rotateCycle c s) = cycleVertices c := by
  classical
  letI : NeZero c.length := ⟨by
    have hc := c.length_ge_two
    omega⟩
  have hlen : (rotateCycle c s).length = c.length := rfl
  change (Finset.univ.image (fun i : Fin c.length => c.vertex (finCycle s i))) =
    Finset.univ.image c.vertex
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨finCycle s i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(finCycle s).symm i, by
      change c.vertex ((finCycle s) ((finCycle s).symm i)) = c.vertex i
      exact congrArg c.vertex ((finCycle s).apply_symm_apply i)⟩

theorem rotate_cycleOccurrences {V : Type u} [Fintype V] {G : MGraph V}
    (c : OccurrenceCycle G) (s : Fin c.length) :
    cycleOccurrences (rotateCycle c s) = cycleOccurrences c := by
  classical
  letI : NeZero c.length := ⟨by
    have hc := c.length_ge_two
    omega⟩
  have hlen : (rotateCycle c s).length = c.length := rfl
  change (Finset.univ.image (fun i : Fin c.length => c.edge (finCycle s i))) =
    Finset.univ.image c.edge
  ext e
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨finCycle s i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(finCycle s).symm i, by
      change c.edge ((finCycle s) ((finCycle s).symm i)) = c.edge i
      exact congrArg c.edge ((finCycle s).apply_symm_apply i)⟩

theorem rotate_last_to {V : Type u} [Fintype V] {G : MGraph V}
    (c : OccurrenceCycle G) (j : Fin c.length) :
    letI : NeZero c.length := ⟨by
      have hc := c.length_ge_two
      omega⟩
    finCycle (j - (⟨c.length - 1, by have hc := c.length_ge_two; omega⟩ : Fin c.length))
      (⟨c.length - 1, by have hc := c.length_ge_two; omega⟩ : Fin c.length) = j := by
  letI : NeZero c.length := ⟨by
    have hc := c.length_ge_two
    omega⟩
  simp [finCycle_apply]

end ThLean.W.S363

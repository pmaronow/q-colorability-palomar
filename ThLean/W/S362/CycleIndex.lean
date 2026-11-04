module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ThLean.W.S362
open ThresholdFoundations
universe u
variable {V : Type u} [Fintype V]
attribute [local instance] Classical.propDecidable

theorem cycleLen_pos {G : MGraph V} (c : OccurrenceCycle G) :
    0 < c.length := by
  exact lt_of_lt_of_le (by decide) c.length_ge_two

def zeroFin (n : ℕ) (hn : 0 < n) : Fin n := ⟨0, hn⟩

theorem nat_rotate_next (n s i : ℕ) :
    (s + ((i + 1) % n)) % n = ((s + i) % n + 1) % n := by
  change s + ((i+1)%n) ≡ (s+i)%n + 1 [MOD n]
  have h1 : s + ((i+1)%n) ≡ s + (i+1) [MOD n] :=
    Nat.ModEq.add_left s (Nat.mod_modEq (i+1) n)
  have h2 : s + (i+1) ≡ s+i+1 [MOD n] := by
    change (s+(i+1))%n = (s+i+1)%n
    rw [← Nat.add_assoc]
  have h3 : s+i+1 ≡ (s+i)%n + 1 [MOD n] :=
    (Nat.ModEq.add_right 1 (Nat.mod_modEq (s+i) n)).symm
  exact h1.trans (h2.trans h3)

def rotateIdx {G : MGraph V} (c : OccurrenceCycle G)
    (s i : Fin c.length) : Fin c.length :=
  ⟨(s.val + i.val) % c.length, Nat.mod_lt _ (cycleLen_pos c)⟩

theorem rotateIdx_injective {G : MGraph V} (c : OccurrenceCycle G)
    (s : Fin c.length) : Function.Injective (rotateIdx c s) := by
  intro i j hij
  apply Fin.ext
  have hmod : s.val + i.val ≡ s.val + j.val [MOD c.length] := by
    change (s.val + i.val) % c.length = (s.val + j.val) % c.length
    exact congrArg Fin.val hij
  have hcancel : i.val ≡ j.val [MOD c.length] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl s.val) hmod
  change i.val % c.length = j.val % c.length at hcancel
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hcancel
  exact hcancel

theorem rotateIdx_surjective {G : MGraph V} (c : OccurrenceCycle G)
    (s : Fin c.length) : Function.Surjective (rotateIdx c s) :=
  Finite.injective_iff_surjective.mp (rotateIdx_injective c s)

theorem rotateIdx_next {G : MGraph V} (c : OccurrenceCycle G)
    (s i : Fin c.length) :
    rotateIdx c s ⟨(i.val + 1) % c.length, Nat.mod_lt _ (cycleLen_pos c)⟩ =
      ⟨((rotateIdx c s i).val + 1) % c.length, Nat.mod_lt _ (cycleLen_pos c)⟩ := by
  apply Fin.ext
  change (s.val + ((i.val+1)%c.length)) % c.length =
    ((s.val+i.val)%c.length + 1) % c.length
  exact nat_rotate_next c.length s.val i.val

def rotateCycle {G : MGraph V} (c : OccurrenceCycle G)
    (s : Fin c.length) : OccurrenceCycle G :=
  { length := c.length
    length_ge_two := c.length_ge_two
    vertex := fun i => c.vertex (rotateIdx c s i)
    edge := fun i => c.edge (rotateIdx c s i)
    vertex_injective := by
      intro i j hij
      exact rotateIdx_injective c s (c.vertex_injective hij)
    edge_injective := by
      intro i j hij
      exact rotateIdx_injective c s (c.edge_injective hij)
    joins := by
      intro i
      change (c.edge (rotateIdx c s i)).1 =
        s(c.vertex (rotateIdx c s i),
          c.vertex (rotateIdx c s ⟨(i.val+1)%c.length, Nat.mod_lt _ (cycleLen_pos c)⟩))
      rw [rotateIdx_next]
      exact c.joins (rotateIdx c s i) }

theorem rotateCycle_vertices {G : MGraph V} (c : OccurrenceCycle G)
    (s : Fin c.length) : cycleVertices (rotateCycle c s) = cycleVertices c := by
  classical
  have hs := rotateIdx_surjective c s
  calc
    cycleVertices (rotateCycle c s) =
        (Finset.univ.image (rotateIdx c s)).image c.vertex := by
          change Finset.univ.image (fun i => c.vertex (rotateIdx c s i)) = _
          rw [Finset.image_image]
          rfl
    _ = cycleVertices c := by
          rw [Finset.image_univ_of_surjective (f := rotateIdx c s) hs]
          rfl

theorem rotateCycle_occurrences {G : MGraph V} (c : OccurrenceCycle G)
    (s : Fin c.length) : cycleOccurrences (rotateCycle c s) = cycleOccurrences c := by
  classical
  have hs := rotateIdx_surjective c s
  calc
    cycleOccurrences (rotateCycle c s) =
        (Finset.univ.image (rotateIdx c s)).image c.edge := by
          change Finset.univ.image (fun i => c.edge (rotateIdx c s i)) = _
          rw [Finset.image_image]
          rfl
    _ = cycleOccurrences c := by
          rw [Finset.image_univ_of_surjective (f := rotateIdx c s) hs]
          rfl

def reverseFin (n : ℕ) (i : Fin n) : Fin n :=
  ⟨n - 1 - i.val, by omega⟩

theorem reverseFin_involutive (n : ℕ) (i : Fin n) :
    reverseFin n (reverseFin n i) = i := by
  apply Fin.ext
  simp [reverseFin]
  omega

theorem reverseFin_injective (n : ℕ) : Function.Injective (reverseFin n) := by
  intro i j hij
  have h := congrArg (reverseFin n) hij
  simpa [reverseFin_involutive] using h

theorem reverseFin_surjective (n : ℕ) : Function.Surjective (reverseFin n) := by
  intro i
  exact ⟨reverseFin n i, reverseFin_involutive n i⟩

def reversePath {G : MGraph V} (p : OccurrencePath G) : OccurrencePath G :=
  { length := p.length
    vertex := fun i => p.vertex (reverseFin (p.length + 1) i)
    edge := fun i => p.edge (reverseFin p.length i)
    vertex_injective := p.vertex_injective.comp (reverseFin_injective (p.length+1))
    edge_injective := p.edge_injective.comp (reverseFin_injective p.length)
    joins := by
      intro i
      let j := reverseFin p.length i
      let i₀ : Fin (p.length+1) := ⟨i.val, by omega⟩
      let i₁ : Fin (p.length+1) := ⟨i.val+1, by omega⟩
      have hji : reverseFin (p.length+1) i₀ =
          ⟨j.val+1, by omega⟩ := by
        apply Fin.ext
        simp [i₀, j, reverseFin]
        omega
      have hjnext : reverseFin (p.length+1) i₁ =
          ⟨j.val, by omega⟩ := by
        apply Fin.ext
        simp [i₁, j, reverseFin]
        omega
      calc
        (p.edge j).1 = s(p.vertex ⟨j.val, by omega⟩,
            p.vertex ⟨j.val+1, by omega⟩) := p.joins j
        _ = s(p.vertex (reverseFin (p.length+1) i₀),
            p.vertex (reverseFin (p.length+1) i₁)) := by
              rw [hji, hjnext]
              exact Sym2.eq_swap }

theorem pathVertices_reverse {G : MGraph V} (p : OccurrencePath G) :
    pathVertices (reversePath p) = pathVertices p := by
  classical
  calc
    pathVertices (reversePath p) =
        (Finset.univ.image (reverseFin (p.length+1))).image p.vertex := by
          change Finset.univ.image (fun i => p.vertex (reverseFin (p.length+1) i)) = _
          rw [Finset.image_image]
          rfl
    _ = pathVertices p := by
          rw [Finset.image_univ_of_surjective (f := reverseFin (p.length+1))
            (reverseFin_surjective (p.length+1))]
          rfl

theorem pathOccurrences_reverse {G : MGraph V} (p : OccurrencePath G) :
    pathOccurrences (reversePath p) = pathOccurrences p := by
  classical
  calc
    pathOccurrences (reversePath p) =
        (Finset.univ.image (reverseFin p.length)).image p.edge := by
          change Finset.univ.image (fun i => p.edge (reverseFin p.length i)) = _
          rw [Finset.image_image]
          rfl
    _ = pathOccurrences p := by
          rw [Finset.image_univ_of_surjective (f := reverseFin p.length)
            (reverseFin_surjective p.length)]
          rfl

theorem reversePath_from {G : MGraph V} (p : OccurrencePath G) (a b : V)
    (h : PathFrom p a b) : PathFrom (reversePath p) b a := by
  rcases h with ⟨h₀, h₁⟩
  constructor
  · simpa [PathFrom, reversePath, reverseFin] using h₁
  · simpa [PathFrom, reversePath, reverseFin] using h₀


end ThLean.W.S362

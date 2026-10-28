import ThLean.BP.S3.Graph

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u

namespace ThLean.W.S308
open ThresholdFoundations
open ThLean.BP.S3

private def pairPerm {V : Type u} (π : Equiv.Perm V) : Pair V ≃ Pair V where
  toFun e := ⟨Sym2.map π e.val, by
    intro v hv
    have he : e.val = s(π.symm v, π.symm v) := by
      calc
        e.val = Sym2.map π.symm (Sym2.map π e.val) := by
          rw [Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id]
          rfl
        _ = Sym2.map π.symm (s(v,v)) := congrArg (Sym2.map π.symm) hv
        _ = s(π.symm v, π.symm v) := by simp
    exact e.property (π.symm v) he⟩
  invFun e := ⟨Sym2.map π.symm e.val, by
    intro v hv
    have he : e.val = s(π v, π v) := by
      calc
        e.val = Sym2.map π (Sym2.map π.symm e.val) := by
          rw [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id]
          rfl
        _ = Sym2.map π (s(v,v)) := congrArg (Sym2.map π) hv
        _ = s(π v, π v) := by simp
    exact e.property (π v) he⟩
  left_inv e := by
    apply Subtype.ext
    change Sym2.map π.symm (Sym2.map π e.val) = e.val
    rw [Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id]
    rfl
  right_inv e := by
    apply Subtype.ext
    change Sym2.map π (Sym2.map π.symm e.val) = e.val
    rw [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id]
    rfl

private theorem pairPerm_val {V : Type u} (π : Equiv.Perm V) (e : Pair V) :
    (pairPerm π e).val = Sym2.map π e.val := rfl

private theorem frozenPair_relabel_iff {V : Type u} [Fintype V] (q : ℕ)
    (hq : 2 ≤ q) (h9b : S3_09bStatement.{u,u})
    (π : Equiv.Perm V) (G : MGraph V) (e : Pair V) :
    FrozenPair q (relabel π G) (pairPerm π e) ↔ FrozenPair q G e := by
  have hclasses := (h9b V V q hq).2.1
  constructor
  · rintro ⟨a,b,hab,hf⟩
    have hab' : e.val = s(π.symm a, π.symm b) := by
      have h := congrArg (Sym2.map π.symm) hab
      calc
        e.val = Sym2.map π.symm (Sym2.map π e.val) := by
          rw [Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id]
          rfl
        _ = Sym2.map π.symm (s(a,b)) := h
        _ = s(π.symm a, π.symm b) := by simp
    have hbmem : b ∈ frozenClass q (relabel π G) a := by
      simpa [frozenClass] using hf
    have hc := hclasses G π (π.symm a)
    have hc' : frozenClass q (relabel π G) a = (frozenClass q G (π.symm a)).image π := by
      simpa only [Equiv.apply_symm_apply] using hc
    rw [hc'] at hbmem
    rcases Finset.mem_image.mp hbmem with ⟨b', hb'mem, hb'eq⟩
    have hb' : b' = π.symm b := by
      apply π.injective
      simpa [Equiv.apply_symm_apply] using hb'eq
    have hf' : Frozen q G (π.symm a) (π.symm b) := by
      have hmem : π.symm b ∈ frozenClass q G (π.symm a) := by
        simpa [hb'] using hb'mem
      simpa [frozenClass] using hmem
    exact ⟨π.symm a, π.symm b, hab', hf'⟩
  · rintro ⟨a,b,hab,hf⟩
    have hab' : (pairPerm π e).val = s(π a, π b) := by
      rw [pairPerm_val, hab]
      simp
    have hbmem : b ∈ frozenClass q G a := by
      simpa [frozenClass] using hf
    have hc := hclasses G π a
    have hbmem' : π b ∈ frozenClass q (relabel π G) (π a) := by
      rw [hc]
      exact Finset.mem_image.mpr ⟨b, hbmem, rfl⟩
    have hf' : Frozen q (relabel π G) (π a) (π b) := by
      simpa [frozenClass] using hbmem'
    exact ⟨π a, π b, hab', hf'⟩

theorem S3_12Statement_of_deps (h9b : S3_09bStatement.{u,u}) :
    S3_12Statement.{u} := by
  intro V _ q hq hV
  refine ⟨?_, ?_, ?_⟩
  · intro G C hC
    constructor
    · unfold classMass
      change ((C.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 ≤
        ∑ D ∈ frozenClasses q G, ((D.card : ℝ) / (Fintype.card V : ℝ)) ^ 2
      exact Finset.single_le_sum
        (s := frozenClasses q G)
        (f := fun D : Finset V => ((D.card : ℝ) / (Fintype.card V : ℝ)) ^ 2)
        (fun D hD => sq_nonneg ((D.card : ℝ) / (Fintype.card V : ℝ))) hC
    · have hn : (0 : ℝ) < (Fintype.card V : ℝ) := by
        exact_mod_cast (show 0 < Fintype.card V by omega)
      have hroot :
          (C.card : ℝ) / (Fintype.card V : ℝ) ≤ Real.sqrt (classMass q G) :=
        Real.le_sqrt_of_sq_le (show
          ((C.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 ≤ classMass q G from
          (by
            unfold classMass
            change ((C.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 ≤
              ∑ D ∈ frozenClasses q G, ((D.card : ℝ) / (Fintype.card V : ℝ)) ^ 2
            exact Finset.single_le_sum
              (s := frozenClasses q G)
              (f := fun D : Finset V => ((D.card : ℝ) / (Fintype.card V : ℝ)) ^ 2)
              (fun D hD => sq_nonneg ((D.card : ℝ) / (Fintype.card V : ℝ))) hC))
      calc
        (C.card : ℝ) = ((C.card : ℝ) / (Fintype.card V : ℝ)) *
            (Fintype.card V : ℝ) := by
          field_simp [ne_of_gt hn]
        _ ≤ (Fintype.card V : ℝ) * Real.sqrt (classMass q G) :=
          (mul_le_mul_of_nonneg_right hroot hn.le).trans_eq (mul_comm _ _)
  · intro A G
    constructor
    · unfold kappaKind uniformProb uniformMean
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro e he
        by_cases h : FrozenPair q G e ∧ A G e <;> simp [indicator, h]
      · exact Nat.cast_nonneg _
    constructor
    · unfold kappaKind kappa uniformProb uniformMean
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum
        intro e he
        by_cases h : FrozenPair q G e
        · by_cases ha : A G e <;> simp [indicator, h, ha]
        · simp [indicator, h]
      · exact Nat.cast_nonneg _
    · intro hG
      simp [kappaKind, uniformProb, uniformMean, indicator, FrozenPair, Frozen, hG]
  · intro A hA π G
    have hs :
        (∑ e : Pair V,
          indicator (FrozenPair q (relabel π G) e ∧ A (relabel π G) e)) =
        (∑ e : Pair V, indicator (FrozenPair q G e ∧ A G e)) := by
      calc
        _ = ∑ e : Pair V,
            indicator (FrozenPair q (relabel π G) (pairPerm π e) ∧
              A (relabel π G) (pairPerm π e)) := by
                symm
                exact Equiv.sum_comp (pairPerm π)
                  (fun e : Pair V => indicator
                    (FrozenPair q (relabel π G) e ∧ A (relabel π G) e))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro e he
          have hf := frozenPair_relabel_iff q hq h9b π G e
          have ha := hA π G e (pairPerm π e) (by rfl)
          simp [indicator, hf, ha]
    unfold kappaKind uniformProb uniformMean
    rw [hs]

end ThLean.W.S308

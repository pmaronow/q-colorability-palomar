module

public import ThLean.BP.S5.Completion

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S503
open ThresholdFoundations
open ThLean.BP.S5

private theorem completionKernel_equivariant
    {V : Type} [Fintype V] (D : ℕ) (π : Equiv.Perm V)
    (x : Fin D → V) (Z : UniformSubset V D) :
    ThLean.BP.S5.completionKernel D (List.ofFn (π ∘ x)) (permSubset D π Z) =
      ThLean.BP.S5.completionKernel D (List.ofFn x) Z := by
  have hs : (List.ofFn (π ∘ x)).toFinset =
      (List.ofFn x).toFinset.map π.toEmbedding := by
    ext v
    simp only [List.mem_toFinset, List.mem_ofFn, Finset.mem_map, Function.comp_apply]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨x i, ⟨i, rfl⟩, hi⟩
    · rintro ⟨a, ⟨j, hj⟩, ha⟩
      exact ⟨j, by simpa [hj] using ha⟩
  simp only [ThLean.BP.S5.completionKernel,
    ThresholdFoundations.completionKernel, permSubset]
  simp only [hs, Finset.card_map, Finset.map_subset_map]

theorem S5_28BStatement_of_deps
    (h27 : ThLean.BP.S5.S5_27Statement)
    (h28A : ThLean.BP.S5.S5_28AStatement)
    (hfinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0}) :
    ThLean.BP.S5.S5_28BStatement := by
  intro V _ _ D hD hDV
  constructor
  · intro π x Z
    exact completionKernel_equivariant D π x Z
  · intro Z
    let μ : UniformSubset V D → ℝ := fun Z =>
      uniformMean (fun x : Fin D → V => ThLean.BP.S5.completionKernel D (List.ofFn x) Z)
    have hμ_nonneg : ∀ Z, 0 ≤ μ Z := by
      intro Z
      dsimp [μ, uniformMean]
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro x hx
        exact (h28A V D hD hDV x).2.2.2.1 Z
      · exact_mod_cast (Nat.zero_le (Fintype.card (Fin D → V)))
    have hμ_sum : (∑ Z : UniformSubset V D, μ Z) = 1 := by
      dsimp [μ, uniformMean]
      rw [← Finset.sum_div, Finset.sum_comm]
      have hcard : (Fintype.card (Fin D → V) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
      apply (div_eq_iff hcard).2
      simp only [one_mul]
      calc
        (∑ x : Fin D → V, ∑ Z : UniformSubset V D,
            ThLean.BP.S5.completionKernel D (List.ofFn x) Z) =
            ∑ x : Fin D → V, 1 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (h28A V D hD hDV x).2.2.1
        _ = (Fintype.card (Fin D → V) : ℝ) := by simp
    have hμ_invariant : ∀ (π : Equiv.Perm V) Z,
        μ (permSubset D π Z) = μ Z := by
      intro π Z
      let e : (Fin D → V) ≃ (Fin D → V) := Equiv.arrowCongr (Equiv.refl (Fin D)) π
      have hreindex := hfinite.1 (Fin D → V) (Fin D → V) e
        (fun x => ThLean.BP.S5.completionKernel D (List.ofFn x) (permSubset D π Z))
      calc
        μ (permSubset D π Z) =
            uniformMean (fun x : Fin D → V =>
              ThLean.BP.S5.completionKernel D (List.ofFn x) (permSubset D π Z)) := rfl
        _ = uniformMean (fun x : Fin D → V =>
              ThLean.BP.S5.completionKernel D (List.ofFn (π ∘ x)) (permSubset D π Z)) := by
              symm
              exact hreindex
        _ = uniformMean (fun x : Fin D → V =>
              ThLean.BP.S5.completionKernel D (List.ofFn x) Z) := by
              unfold uniformMean
              congr 1
              apply Finset.sum_congr rfl
              intro x hx
              exact completionKernel_equivariant D π x Z
        _ = μ Z := rfl
    have h27all := h27 V D hDV
    have huniform := h27all.2.2.2 μ hμ_nonneg hμ_sum hμ_invariant Z
    simpa [h27all.1] using huniform

end ThLean.W.S503

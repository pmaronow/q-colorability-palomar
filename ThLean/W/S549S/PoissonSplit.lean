import ThLean.W.S549S.EdgeBlocks
import ThLean.W.S549.PoissonSplit

noncomputable section
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S549S
open ThresholdFoundations ThLean.BP.S5

/-- Splitting independent edge counts preserves every multiplicity. -/
theorem countMean_partition {A B V : Type} [Fintype A] [Fintype B] [Fintype V]
    (e : A ⊕ B ≃ V) (r : ℝ) (hr : 0 ≤ r) (f : MGraph V → ℝ)
    (hf : ∃ C : ℝ, ∀ G, |f G| ≤ C) :
    countMean r f =
      countMean r (fun GB : MGraph B =>
        countMean r (fun GA : MGraph A =>
          ∑' c : (A × B) → ℕ, (∏ p, poissonWeight r (c p)) *
            f (mapGraph (fun b => e (Sum.inr b)) GB +
              mapGraph (fun a => e (Sum.inl a)) GA +
              (fun q => ∑ p : A × B,
                if q = s(e (Sum.inl p.1), e (Sum.inr p.2)) then c p else 0)))) := by
  classical
  let rB : Sym2 B → ℝ := perPairRate r
  let rA : Sym2 A → ℝ := perPairRate r
  let rates : EdgeBlocks A B → ℝ := Sum.elim rB (Sum.elim rA (fun _ => r))
  let F : (EdgeBlocks A B → ℕ) → ℝ :=
    fun x => f (fun q => x ((edgeEquiv e).symm q))
  have hB : ∀ i, 0 ≤ rB i := by
    intro i
    dsimp [rB, perPairRate]
    split_ifs <;> positivity
  have hA : ∀ i, 0 ≤ rA i := by
    intro i
    dsimp [rA, perPairRate]
    split_ifs <;> positivity
  have hrest : ∀ i, 0 ≤ Sum.elim rA (fun _ : A × B => r) i := by
    rintro (i | i)
    · exact hA i
    · exact hr
  have hrates : ∀ i, 0 ≤ rates i := by
    rintro (i | i)
    · exact hB i
    · exact hrest i
  have he : (fun k => perPairRate r (edgeEquiv e k)) = rates := by
    funext k
    rcases k with i | (i | i)
    · exact edgeEquiv_rate_outside e r i
    · exact edgeEquiv_rate_inside e r i
    · exact edgeEquiv_rate_crossing e r i
  obtain ⟨C, hC⟩ := hf
  have hF : ∃ C : ℝ, ∀ x, |F x| ≤ C := ⟨C, fun x => hC _⟩
  calc
    countMean r f = coordinateMean rates F := by
      change coordinateMean (perPairRate r) f = _
      rw [coordinateMean_equiv (edgeEquiv e), he]
    _ = coordinateMean rB (fun GB =>
          coordinateMean (Sum.elim rA (fun _ : A × B => r))
            (fun x => F (Sum.elim GB x))) :=
      coordinateMean_sum rates hrates F hF
    _ = coordinateMean rB (fun GB => coordinateMean rA (fun GA =>
          coordinateMean (fun _ : A × B => r)
            (fun c => F (Sum.elim GB (Sum.elim GA c))))) := by
      congr 1
      funext GB
      exact coordinateMean_sum _ hrest _ ⟨C, fun x => hC _⟩
    _ = _ := by
      change coordinateMean rB _ = coordinateMean rB _
      congr 1
      funext GB
      change coordinateMean rA _ = coordinateMean rA _
      congr 1
      funext GA
      unfold coordinateMean coordinateMass
      apply tsum_congr
      intro c
      change (∏ p, poissonWeight r (c p)) * f (assemble e GB GA c) = _
      rw [assemble_formula]

/-- Independent Poisson edge counts factor over the two vertex blocks and their crossing pairs. -/
theorem countMeanPartitionFactorization_holds :
    ThLean.Contrib.S549.S549_CountMeanPartitionFactorizationStatement := by
  intro V _ A B _ _ e _ _ r hr f hf
  exact countMean_partition e r hr f hf

/-- The partitioned count law and the histogram law give the Poisson splitting identity. -/
theorem S5_09AStatement_of_deps (h08b : S5_08BStatement) : S5_09AStatement :=
  ThLean.W.S549.S5_09AStatement_of_08B_and_count_factorization h08b
    countMeanPartitionFactorization_holds

example (h08b : S5_08BStatement) : ThLean.BP.S5.S5_09AStatement :=
  S5_09AStatement_of_deps h08b

end ThLean.W.S549S

import ThLean.W.SA51S.Global
import ThLean.W.SA51S.Blocks
import ThLean.W.SA51S.Tensor
import ThLean.W.SA51S.Poisson

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA51S
open ThresholdFoundations ThLean.BP.SA

def pairOp (n₁ n₂ : ℕ) :
    Module.End ℝ (MGraph (Fin n₁) × MGraph (Fin n₂) → ℝ) :=
  ((n₁ : ℝ) / (n₁+n₂ : ℕ)) •
    leftOp (Y := MGraph (Fin n₂))
      (fun (G : MGraph (Fin n₁)) (xy : Fin n₁ × Fin n₁) => addEdge G s(xy.1,xy.2)) +
  ((n₂ : ℝ) / (n₁+n₂ : ℕ)) •
    rightOp (X := MGraph (Fin n₁))
      (fun (H : MGraph (Fin n₂)) (xy : Fin n₂ × Fin n₂) => addEdge H s(xy.1,xy.2))

lemma local_iterate_blocks (n₁ n₂ m : ℕ) (f : MGraph (Fin (n₁+n₂)) → ℝ)
    (G : MGraph (Fin n₁)) (H : MGraph (Fin n₂)) :
    ((localStep n₁ n₂)^[m]) f (blockGraph G H) =
      (pairOp n₁ n₂ ^ m) (fun z => f (blockGraph z.1 z.2)) (G,H) := by
  induction m generalizing G H with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    change (n₁ : ℝ) / (n₁+n₂ : ℕ) *
        uniformMean (fun xy : Fin n₁ × Fin n₁ => ((localStep n₁ n₂)^[m]) f
          (addEdge (blockGraph G H) s(leftVertex n₁ n₂ xy.1,leftVertex n₁ n₂ xy.2))) +
      (n₂ : ℝ) / (n₁+n₂ : ℕ) *
        uniformMean (fun xy : Fin n₂ × Fin n₂ => ((localStep n₁ n₂)^[m]) f
          (addEdge (blockGraph G H) s(rightVertex n₁ n₂ xy.1,rightVertex n₁ n₂ xy.2))) = _
    simp_rw [← blockGraph_add_left, ← blockGraph_add_right, ih]
    rfl

lemma block_indicator (q n₁ n₂ : ℕ) :
    (fun z : MGraph (Fin n₁) × MGraph (Fin n₂) =>
      indicator (Colorable q (blockGraph z.1 z.2))) =
    (fun z => indicator (Colorable q z.1) * indicator (Colorable q z.2)) := by
  funext z
  rw [blockGraph_colorable]
  by_cases h₁ : Colorable q z.1 <;> by_cases h₂ : Colorable q z.2 <;>
    simp [indicator, h₁, h₂]

lemma local_binomial (q n₁ n₂ m : ℕ) :
    ((localStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0 =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
        (m.choose ij.1 : ℝ) * ((n₁ : ℝ)/(n₁+n₂ : ℕ)) ^ ij.1 *
          ((n₂ : ℝ)/(n₁+n₂ : ℕ)) ^ ij.2 *
            ((edgeOp n₁ ^ ij.1) (fun G => indicator (Colorable q G)) 0 *
              (edgeOp n₂ ^ ij.2) (fun H => indicator (Colorable q H)) 0) := by
  rw [← blockGraph_zero n₁ n₂, local_iterate_blocks, block_indicator]
  simpa only [pairOp, edgeOp] using tensor_binomial
    (fun (G : MGraph (Fin n₁)) (xy : Fin n₁ × Fin n₁) => addEdge G s(xy.1,xy.2))
    (fun (H : MGraph (Fin n₂)) (xy : Fin n₂ × Fin n₂) => addEdge H s(xy.1,xy.2))
    (fun G => indicator (Colorable q G)) (fun H => indicator (Colorable q H))
    ((n₁ : ℝ) / (n₁+n₂ : ℕ)) ((n₂ : ℝ) / (n₁+n₂ : ℕ)) m 0 0

lemma edge_iterate_bounds (q n m : ℕ) (hn : 1 ≤ n) (G : MGraph (Fin n)) :
    0 ≤ (edgeOp n ^ m) (fun H => indicator (Colorable q H)) G ∧
      (edgeOp n ^ m) (fun H => indicator (Colorable q H)) G ≤ 1 := by
  letI : Nonempty (Fin n × Fin n) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  exact averageOp_pow_bounds _ _ (fun _ => indicator_bounds _) m G

lemma edge_mixture (q n : ℕ) (c : ℝ) :
    poissonMixture (c*n) (fun m => (edgeOp n ^ m) (fun G => indicator (Colorable q G)) 0) =
      rho q n c := by
  unfold poissonMixture rho
  apply tsum_congr
  intro m
  congr 1
  simpa [uniformProb] using edgeOp_pow n m (fun G => indicator (Colorable q G)) 0

lemma local_mixture (q n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (c : ℝ) (hc : 0 ≤ c) :
    poissonMixture (c*(n₁+n₂ : ℕ))
      (fun m => ((localStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0) =
      rho q n₁ c * rho q n₂ c := by
  have h₁ : (0 : ℝ) < n₁ := by exact_mod_cast (show 0 < n₁ by omega)
  have h₂ : (0 : ℝ) < n₂ := by exact_mod_cast (show 0 < n₂ by omega)
  simp_rw [local_binomial, Nat.cast_add]
  rw [poisson_convolution c (n₁ : ℝ) (n₂ : ℝ) hc h₁ h₂ _ _
    (fun m => edge_iterate_bounds q n₁ m hn₁ 0)
    (fun m => edge_iterate_bounds q n₂ m hn₂ 0)]
  rw [edge_mixture, edge_mixture]

end ThLean.W.SA51S

module

public import ThLean.W.S390S.Atoms
public import ThLean.W.S390S.Lists

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S390S
open ThresholdFoundations ThLean.BP.S3
universe u v
set_option maxHeartbeats 1000000

/-- The nonnegative split expectation follows from the joint ordered-word
atom law and the scalar Poisson weights. -/
theorem S3_37cStatement_of_deps
    (h31 : S3_31Statement) (h37 : S3_37aStatement.{max u v}) :
    S3_37cStatement.{u,v} := by
  intro A B instA instB hTotal hB t h ht
  letI : Nonempty B := Fintype.card_pos_iff.mp (by omega)
  let rA : ℝ := t * ((Fintype.card A).choose 2 : ℝ) /
    ((Fintype.card (A ⊕ B)).choose 2 : ℝ)
  let rB : ℝ := t * ((Fintype.card B).choose 2 : ℝ) /
    ((Fintype.card (A ⊕ B)).choose 2 : ℝ)
  let rX : ℝ := t * Fintype.card B / ((Fintype.card (A ⊕ B)).choose 2 : ℝ)
  have hrA : 0 ≤ rA := by dsimp [rA]; positivity
  have hrB : 0 ≤ rB := by dsimp [rB]; positivity
  have hrX : 0 ≤ rX := by dsimp [rX]; positivity
  let F : List (Pair (A ⊕ B)) → MGraph A × MGraph B × (A → List B) :=
    fun w => (restrictLeft (listGraph w), restrictRight (listGraph w), splitNeighbors w)
  let f : MGraph A × MGraph B × (A → List B) → ℝ≥0∞ :=
    fun y => h (splitUnionGraph y.1 y.2.1 y.2.2)
  have hAtom (GA : MGraph A) (GB : MGraph B) (xs : A → List B) :
      ENNReal.ofReal (poissonWordProb t (fun w => F w = (GA,GB,xs))) =
        ENNReal.ofReal (poissonGraphMean rA (fun G => indicator (G = GA))) *
        ENNReal.ofReal (poissonGraphMean rB (fun G => indicator (G = GB))) *
        ∏ a, ENNReal.ofReal (poissonListMass rX
          (fun _ : B => 1 / (Fintype.card B : ℝ)) (xs a)) := by
    simp only [F, Prod.mk.injEq]
    rw [split_atom h37 hTotal hB t ht GA GB xs]
    change ENNReal.ofReal
      ((poissonGraphMean rA (fun G => indicator (G = GA)) *
        poissonGraphMean rB (fun G => indicator (G = GB))) *
        ∏ a, poissonListMass rX (fun _ : B => 1 / (Fintype.card B : ℝ)) (xs a)) = _
    rw [ENNReal.ofReal_mul (mul_nonneg (poissonGraphProb_nonneg h31 rA hrA GA)
      (poissonGraphProb_nonneg h31 rB hrB GB)),
      ENNReal.ofReal_mul (poissonGraphProb_nonneg h31 rA hrA GA),
      ENNReal.ofReal_prod_of_nonneg (fun a _ => uniformListMass_nonneg h31 rX hrX (xs a))]
  calc
    poissonGraphMeanENN t h = wordMeanENN t (fun w => f (F w)) := by
      unfold poissonGraphMeanENN wordMeanENN
      congr 1
      funext m
      congr 1
      funext x
      dsimp only [F, f]
      rw [splitUnionGraph_reconstruct, ThLean.W.S339.listGraph_ofFn]
    _ = ∑' y : MGraph A × MGraph B × (A → List B),
        ENNReal.ofReal (poissonWordProb t (fun w => F w = y)) * f y :=
      wordMeanENN_atoms h31 t ht F f
    _ = ∑' GA : MGraph A, ∑' GB : MGraph B, ∑' xs : A → List B,
        (ENNReal.ofReal (poissonGraphMean rA (fun G => indicator (G = GA))) *
        ENNReal.ofReal (poissonGraphMean rB (fun G => indicator (G = GB))) *
        ∏ a, ENNReal.ofReal (poissonListMass rX
          (fun _ : B => 1 / (Fintype.card B : ℝ)) (xs a))) *
        h (splitUnionGraph GA GB xs) := by
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro GA
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro GB
      apply tsum_congr
      intro xs
      rw [hAtom]
    _ = poissonGraphMeanENN rA (fun GA : MGraph A =>
        poissonGraphMeanENN rB (fun GB : MGraph B => independentPoissonListsMeanENN rX
          (fun xs : A → List B => h (splitUnionGraph GA GB xs)))) := by
      symm
      rw [graphMeanENN_atoms h31 rA hrA]
      simp_rw [graphMeanENN_atoms h31 rB hrB, independentLists_atoms h31 rX hrX,
        ← ENNReal.tsum_mul_left]
      simp only [mul_assoc]

example (h31 : S3_31Statement) (h37 : S3_37aStatement.{max u v}) :
    ThLean.BP.S3.S3_37cStatement.{u,v} := S3_37cStatement_of_deps h31 h37

end ThLean.W.S390S

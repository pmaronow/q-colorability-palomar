module

public import ThLean.W.S523S.Kernels
public import ThLean.W.S523S.Measurability

@[expose] public section

/-!
The finite-average helpers `uniformMean_add`, `uniformMean_comm`
match implementation patterns in OpenAI's math library (Apache-2.0).
Local versions use project-specific averaging definitions and namespaces.
Their source credits and licence scope are listed in NOTICE; the licence
text is in LICENSES/Apache-2.0.txt.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S529S
open ThresholdFoundations ThLean.BP.S5
open ThLean.W.S523S

theorem uniformMean_nonneg {A : Type} [Fintype A] {f : A → ℝ}
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f :=
  div_nonneg (Finset.sum_nonneg (fun a _ => hf a)) (Nat.cast_nonneg _)

theorem uniformMean_mono {A : Type} [Fintype A] {f g : A → ℝ}
    (hfg : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => hfg a))
    (Nat.cast_nonneg _)

theorem uniformMean_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by positivity
  simp [uniformMean, hc]

theorem uniformMean_add {A : Type} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_range {A : Type} [Fintype A] {f : A → ℝ}
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 := by
  refine ⟨uniformMean_nonneg (fun a => (hf a).1), ?_⟩
  by_cases hA : Nonempty A
  · let := hA
    exact (uniformMean_mono (fun a => (hf a).2)).trans_eq (uniformMean_const 1)
  · have : IsEmpty A := not_nonempty_iff.mp hA
    simp [uniformMean]

theorem indicator_range (P : Prop) : 0 ≤ indicator P ∧ indicator P ≤ 1 := by
  by_cases hP : P <;> simp [indicator, hP]

theorem uniformMean_comm {A B : Type} [Fintype A] [Fintype B]
    (f : A → B → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  simp only [uniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem mixture_summable {s : ℝ} (hs : 0 ≤ s) {b : ℕ → ℝ}
    (hb : ∀ m, 0 ≤ b m ∧ b m ≤ 1) :
    Summable (fun m => poissonWeight s m * b m) := by
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (weight_nonneg hs m) (hb m).1)
    (fun m => ?_) (weight_hasSum s).summable
  exact mul_le_of_le_one_right (weight_nonneg hs m) (hb m).2

theorem mixture_uniformMean_comm {A : Type} [Fintype A]
    {s : ℝ} (hs : 0 ≤ s) (b : A → ℕ → ℝ)
    (hb : ∀ a m, 0 ≤ b a m ∧ b a m ≤ 1) :
    poissonMixture s (fun m => uniformMean (fun a => b a m)) =
      uniformMean (fun a => poissonMixture s (b a)) := by
  unfold poissonMixture uniformMean
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [tsum_div_const]
  congr 1
  exact Summable.tsum_finsetSum (fun a _ => mixture_summable hs (hb a))

theorem graphMean_uniformMean_comm {V A : Type} [Fintype V] [Fintype A]
    {s : ℝ} (hs : 0 ≤ s) (f : A → MGraph V → ℝ)
    (hf : ∀ a G, 0 ≤ f a G ∧ f a G ≤ 1) :
    poissonGraphMean s (fun G => uniformMean (fun a => f a G)) =
      uniformMean (fun a => poissonGraphMean s (f a)) := by
  unfold poissonGraphMean
  simp_rw [uniformMean_comm (fun (x : EdgeTuple V _) a => f a (tupleGraph x))]
  apply mixture_uniformMean_comm hs
  intro a m
  exact uniformMean_range (fun x => hf a (tupleGraph x))

theorem discrepancy_average (q N D : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    discrepancy q N D s =
      uniformMean (fun Z : UniformSubset (Fin N) D =>
        poissonGraphMean s (fun G : MGraph (Fin N) =>
          indicator (Colorable q G ∧ ¬ Colorable q (identify G Z.val)))) := by
  exact graphMean_uniformMean_comm hs _ (fun _ _ => indicator_range _)

theorem graphMean_nonneg {V : Type} [Fintype V] {s : ℝ} (hs : 0 ≤ s)
    {f : MGraph V → ℝ} (hf : ∀ G, 0 ≤ f G) : 0 ≤ poissonGraphMean s f := by
  apply tsum_nonneg
  intro m
  exact mul_nonneg (weight_nonneg hs m) (uniformMean_nonneg (fun x => hf _))

theorem blockingMean_range {V : Type} [Fintype V] (q : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (j : ℕ) :
    0 ≤ blockingMean (V := V) q r j ∧ blockingMean (V := V) q r j ≤ 1 := by
  have hb (B : MGraph V) : 0 ≤ blocking q B j ∧ blocking q B j ≤ 1 :=
    uniformMean_range (fun _ => indicator_range _)
  have hab (B : MGraph V) : |blocking q B j| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(hb B).1], (hb B).2⟩
  change 0 ≤ mean (perPairRate r) (fun B => blocking q B j) ∧
    mean (perPairRate r) (fun B => blocking q B j) ≤ 1
  refine ⟨mean_nonneg (perPairRate_nonneg hr) (fun B => (hb B).1), ?_⟩
  calc
    _ ≤ mean (perPairRate r) (fun _ => 1) :=
      mean_mono (perPairRate_nonneg hr) ⟨1, hab⟩ ⟨1, by simp⟩
        (fun B => (hb B).2)
    _ = 1 := mean_const (perPairRate_nonneg hr) 1

theorem integral_uniformMean {A : Type} [Fintype A] (f : A → ℝ → ℝ)
    (a b : ℝ) (hf : ∀ x, IntervalIntegrable (f x) volume a b) :
    (∫ s in a..b, uniformMean (fun x => f x s)) =
      uniformMean (fun x => ∫ s in a..b, f x s) := by
  unfold uniformMean
  rw [intervalIntegral.integral_div]
  congr 1
  exact intervalIntegral.integral_finsetSum (fun x _ => hf x)

end ThLean.W.S529S

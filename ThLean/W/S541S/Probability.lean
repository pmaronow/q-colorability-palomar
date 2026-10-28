import ThLean.BP.S5.Occupation

/-!
The finite-average helpers `uniformMean_mono`, `uniformMean_nonneg`
match implementation patterns in OpenAI's math library (Apache-2.0).
Local versions use project-specific averaging definitions and namespaces.
Their source credits and licence scope are listed in NOTICE; the licence
text is in LICENSES/Apache-2.0.txt.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S541S
open ThresholdFoundations ThLean.BP.S5

theorem indicator_bounds (P : Prop) : 0 ≤ indicator P ∧ indicator P ≤ 1 := by
  by_cases h : P <;> simp [indicator, h]

theorem indicator_mono {P Q : Prop} (h : P → Q) : indicator P ≤ indicator Q := by
  by_cases hp : P
  · simp [indicator, hp, h hp]
  · simpa [indicator, hp] using (indicator_bounds Q).1

theorem uniformMean_mono {A : Type*} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

theorem uniformMean_nonneg {A : Type*} [Fintype A] {f : A → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

theorem uniformMean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  simp [uniformMean, Fintype.card_ne_zero]

theorem uniformMean_bounds {A : Type*} [Fintype A] [Nonempty A]
    {f : A → ℝ} (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 := by
  refine ⟨uniformMean_nonneg fun a => (hf a).1, ?_⟩
  exact (uniformMean_mono fun a => (hf a).2).trans_eq (uniformMean_const 1)

theorem uniformMean_finset_sum {A I : Type*} [Fintype A] (s : Finset I)
    (c : I → ℝ) (f : I → A → ℝ) :
    uniformMean (fun a => ∑ i ∈ s, c i * f i a) =
      ∑ i ∈ s, c i * uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum, mul_div_assoc]

theorem poissonMixture_bounds (hE01 : S5_E01Statement) {z : ℝ} (hz : 0 ≤ z)
    {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    Summable (fun j => poissonWeight z j * b j) ∧
      0 ≤ poissonMixture z b ∧ poissonMixture z b ≤ 1 :=
  (hE01.1 z hz).2.2.2 1 b zero_le_one hb

theorem poissonMixture_mono (hE01 : S5_E01Statement) {z : ℝ} (hz : 0 ≤ z)
    {f g : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ 1) (hfg : ∀ j, f j ≤ g j) :
    poissonMixture z f ≤ poissonMixture z g := by
  exact (poissonMixture_bounds hE01 hz hf).1.tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (hfg j) ((hE01.1 z hz).1 j).1)
    (poissonMixture_bounds hE01 hz hg).1

theorem poissonGraphMean_bounds {V : Type*} [Fintype V] [Nonempty (Pair V)]
    (hE01 : S5_E01Statement) {t : ℝ} (ht : 0 ≤ t) {f : MGraph V → ℝ}
    (hf : ∀ G, 0 ≤ f G ∧ f G ≤ 1) :
    0 ≤ poissonGraphMean t f ∧ poissonGraphMean t f ≤ 1 := by
  exact (poissonMixture_bounds hE01 ht fun _ => uniformMean_bounds fun _ => hf _).2

theorem poissonGraphMean_mono {V : Type*} [Fintype V] [Nonempty (Pair V)]
    (hE01 : S5_E01Statement) {t : ℝ} (ht : 0 ≤ t) {f g : MGraph V → ℝ}
    (hf : ∀ G, 0 ≤ f G ∧ f G ≤ 1) (hg : ∀ G, 0 ≤ g G ∧ g G ≤ 1)
    (hfg : ∀ G, f G ≤ g G) : poissonGraphMean t f ≤ poissonGraphMean t g := by
  apply poissonMixture_mono hE01 ht
    (fun _ => uniformMean_bounds fun _ => hf _)
    (fun _ => uniformMean_bounds fun _ => hg _)
  intro m
  exact uniformMean_mono fun _ => hfg _

theorem poissonGraphMean_finset_sum {V I : Type*} [Fintype V]
    [Nonempty (Pair V)] (hE01 : S5_E01Statement) {t : ℝ} (ht : 0 ≤ t)
    (s : Finset I) (c : I → ℝ) (f : I → MGraph V → ℝ)
    (hf : ∀ i G, 0 ≤ f i G ∧ f i G ≤ 1) :
    poissonGraphMean t (fun G => ∑ i ∈ s, c i * f i G) =
      ∑ i ∈ s, c i * poissonGraphMean t (f i) := by
  unfold poissonGraphMean poissonMixture
  simp_rw [uniformMean_finset_sum, Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    simp_rw [← mul_assoc, mul_comm (poissonWeight t _) (c i), mul_assoc]
    rw [tsum_mul_left]
  · intro i hi
    have hs := (poissonMixture_bounds hE01 ht
      (fun m => uniformMean_bounds (fun x : EdgeTuple V m => hf i (tupleGraph x)))).1
    simpa only [mul_left_comm] using hs.mul_left (c i)

theorem poissonMixture_truncate (z : ℝ) (D : ℕ) (b : ℕ → ℝ) :
    poissonMixture z (fun j => if j ≤ D then b j else 0) =
      ∑ j ∈ Finset.range (D + 1), poissonWeight z j * b j := by
  unfold poissonMixture
  rw [tsum_eq_sum (s := Finset.range (D + 1))]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjD : j ≤ D := by have := Finset.mem_range.mp hj; omega
    simp [hjD]
  · intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp [show ¬ j ≤ D by omega]

theorem poisson_partial_mass_le_one (hE01 : S5_E01Statement)
    {z : ℝ} (hz : 0 ≤ z) (D : ℕ) :
    (∑ j ∈ Finset.range (D + 1), poissonWeight z j) ≤ 1 := by
  have hw := hE01.1 z hz
  exact (hw.2.1.summable.sum_le_tsum _ (fun j _ => (hw.1 j).1)).trans_eq hw.2.1.tsum_eq

end ThLean.W.S541S

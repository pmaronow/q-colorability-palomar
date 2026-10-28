import ThLean.W.S339.Poisson

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S390S
open ThresholdFoundations ThLean.BP.S3
universe u v
set_option maxHeartbeats 1000000

theorem uniformProb_bounds {X : Type*} [Fintype X] (P : X → Prop) :
    0 ≤ uniformProb P ∧ uniformProb P ≤ 1 := by
  by_cases hX : Nonempty X
  · letI := hX
    have hc : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun x _ => by unfold indicator; split_ifs <;> norm_num)) hc.le
    · change (∑ x, indicator (P x)) / (Fintype.card X : ℝ) ≤ 1
      rw [div_le_one hc]
      calc
        (∑ x, indicator (P x)) ≤ ∑ _x : X, (1 : ℝ) :=
          Finset.sum_le_sum (fun x _ => by unfold indicator; split_ifs <;> norm_num)
        _ = _ := by simp
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    simp [uniformProb, uniformMean]

theorem uniformMeanENN_ofReal {X : Type*} [Fintype X] (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    uniformMeanENN (fun x => ENNReal.ofReal (f x)) = ENNReal.ofReal (uniformMean f) := by
  by_cases hX : Nonempty X
  · letI := hX
    have hc : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
    unfold uniformMeanENN uniformMean
    rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg (fun x _ => hf x)]
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    simp [uniformMeanENN, uniformMean]

def prefixWeight (X : ℕ → Type u) [∀ m, Fintype (X m)] (t : ℝ)
    (p : Σ m, X m) : ℝ≥0∞ :=
  ENNReal.ofReal (poissonWeight t p.1) / Fintype.card (X p.1)

theorem mixtureENN_eq_prefix (X : ℕ → Type u) [∀ m, Fintype (X m)]
    (t : ℝ) (f : (Σ m, X m) → ℝ≥0∞) :
    poissonMixtureENN t (fun m => uniformMeanENN (fun x : X m => f ⟨m,x⟩)) =
      ∑' p : Σ m, X m, prefixWeight X t p * f p := by
  unfold poissonMixtureENN
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro m
  unfold prefixWeight uniformMeanENN
  dsimp only
  rw [tsum_fintype]
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ac_rfl

theorem mixtureENN_indicator (h31 : S3_31Statement)
    (X : ℕ → Type u) [∀ m, Fintype (X m)] (t : ℝ) (ht : 0 ≤ t)
    (P : (Σ m, X m) → Prop) :
    poissonMixtureENN t (fun m => uniformMeanENN
      (fun x : X m => ENNReal.ofReal (indicator (P ⟨m,x⟩)))) =
      ENNReal.ofReal (poissonMixture t (fun m => uniformProb (fun x : X m => P ⟨m,x⟩))) := by
  have hn (m : ℕ) := (uniformProb_bounds (fun x : X m => P ⟨m,x⟩)).1
  have hs : Summable (fun m => poissonWeight t m *
      uniformProb (fun x : X m => P ⟨m,x⟩)) := by
    apply Summable.of_nonneg_of_le (fun m => mul_nonneg ((h31 t ht).1 m) (hn m))
      (fun m => ?_) (h31 t ht).2.1
    exact mul_le_of_le_one_right ((h31 t ht).1 m)
      (uniformProb_bounds (fun x : X m => P ⟨m,x⟩)).2
  unfold poissonMixtureENN poissonMixture
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg ((h31 t ht).1 m) (hn m)) hs]
  apply tsum_congr
  intro m
  dsimp only
  rw [uniformMeanENN_ofReal _ (fun _ => by unfold indicator; split_ifs <;> norm_num),
    ← ENNReal.ofReal_mul ((h31 t ht).1 m)]
  rfl

theorem tsum_comp_atoms {X : Type u} {Y : Type v}
    (p : X → ℝ≥0∞) (F : X → Y) (f : Y → ℝ≥0∞) :
    (∑' x, p x * f (F x)) =
      ∑' y, (∑' x, if F x = y then p x else 0) * f y := by
  symm
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  rw [tsum_eq_single (F x)]
  · simp
  · intro y hy
    simp [Ne.symm hy]

theorem prefixMean_atoms {Y : Type v} (h31 : S3_31Statement)
    (X : ℕ → Type u) [∀ m, Fintype (X m)]
    (t : ℝ) (ht : 0 ≤ t) (F : (Σ m, X m) → Y) (f : Y → ℝ≥0∞) :
    poissonMixtureENN t (fun m => uniformMeanENN (fun x : X m => f (F ⟨m,x⟩))) =
      ∑' y, ENNReal.ofReal (poissonMixture t
        (fun m => uniformProb (fun x : X m => F ⟨m,x⟩ = y))) * f y := by
  rw [mixtureENN_eq_prefix X t (fun p => f (F p)), tsum_comp_atoms]
  apply tsum_congr
  intro y
  congr 1
  calc
    (∑' p : Σ m, X m, if F p = y then prefixWeight X t p else 0) =
        ∑' p : Σ m, X m, prefixWeight X t p * ENNReal.ofReal (indicator (F p = y)) := by
      apply tsum_congr
      intro p
      by_cases hp : F p = y <;> simp [indicator, hp]
    _ = _ := by
      rw [← mixtureENN_eq_prefix X t (fun p => ENNReal.ofReal (indicator (F p = y)))]
      exact mixtureENN_indicator h31 X t ht (fun p => F p = y)

def wordMeanENN {V : Type u} [Fintype V] (t : ℝ)
    (f : List (Pair V) → ℝ≥0∞) : ℝ≥0∞ :=
  poissonMixtureENN t (fun m => uniformMeanENN (fun x : EdgeTuple V m => f (List.ofFn x)))

theorem wordMeanENN_atoms {V : Type u} [Fintype V] {Y : Type v}
    (h31 : S3_31Statement) (t : ℝ) (ht : 0 ≤ t)
    (F : List (Pair V) → Y) (f : Y → ℝ≥0∞) :
    wordMeanENN t (fun w => f (F w)) =
      ∑' y, ENNReal.ofReal (poissonWordProb t (fun w => F w = y)) * f y :=
  prefixMean_atoms h31 (fun m => EdgeTuple V m) t ht (fun p => F (List.ofFn p.2)) f

theorem graphMeanENN_atoms {V : Type u} [Fintype V]
    (h31 : S3_31Statement) (t : ℝ) (ht : 0 ≤ t) (f : MGraph V → ℝ≥0∞) :
    poissonGraphMeanENN t f = ∑' G : MGraph V,
      ENNReal.ofReal (poissonGraphMean t (fun H => indicator (H = G))) * f G :=
  prefixMean_atoms h31 (fun m => EdgeTuple V m) t ht (fun p => tupleGraph p.2) f

theorem poissonGraphProb_nonneg {V : Type*} [Fintype V]
    (h31 : S3_31Statement) (t : ℝ) (ht : 0 ≤ t) (G : MGraph V) :
    0 ≤ poissonGraphMean t (fun H => indicator (H = G)) := by
  exact tsum_nonneg (fun m => mul_nonneg ((h31 t ht).1 m)
    (uniformProb_bounds (fun x : EdgeTuple V m => tupleGraph x = G)).1)

end ThLean.W.S390S

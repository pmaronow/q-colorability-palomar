import ThLean.BP.SA.Alternatives
import ThLean.Contrib.SA51.PoissonMixtureIdentities

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA51
open ThresholdFoundations ThLean.BP.SA

private lemma uniformMean_bounds {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 := by
  unfold uniformMean
  have hc : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty A›
  constructor
  · apply div_nonneg
    · exact Finset.sum_nonneg (fun a _ => h0 a)
    · positivity
  · apply (div_le_iff₀ hc).2
    calc
      (∑ a, f a) ≤ ∑ _a : A, (1 : ℝ) := Finset.sum_le_sum (fun a _ => h1 a)
      _ = (Fintype.card A : ℝ) := by simp
      _ ≤ 1 * (Fintype.card A : ℝ) := by nlinarith

private lemma globalStep_bounds (n₁ n₂ : ℕ) (f : MGraph (Fin (n₁+n₂)) → ℝ)
    (hN : 0 < ((n₁+n₂ : ℕ) : ℝ)) (h0 : ∀ G, 0 ≤ f G) (h1 : ∀ G, f G ≤ 1)
    (G : MGraph (Fin (n₁+n₂))) :
    0 ≤ globalStep n₁ n₂ f G ∧ globalStep n₁ n₂ f G ≤ 1 := by
  have hn : 0 < n₁+n₂ := by exact_mod_cast hN
  letI : Nonempty (Fin (n₁+n₂) × Fin (n₁+n₂)) :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  apply uniformMean_bounds
  · intro xy
    exact h0 _
  · intro xy
    exact h1 _

private lemma localStep_bounds (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (f : MGraph (Fin (n₁+n₂)) → ℝ) (h0 : ∀ G, 0 ≤ f G) (h1 : ∀ G, f G ≤ 1)
    (G : MGraph (Fin (n₁+n₂))) :
    0 ≤ localStep n₁ n₂ f G ∧ localStep n₁ n₂ f G ≤ 1 := by
  have hN : 0 < ((n₁+n₂ : ℕ) : ℝ) := by positivity
  have hA : 0 ≤ (n₁ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) := div_nonneg (by positivity) (le_of_lt hN)
  have hB : 0 ≤ (n₂ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) := div_nonneg (by positivity) (le_of_lt hN)
  have hsum : (n₁ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) +
      (n₂ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) = 1 := by
    have hN' : (n₁+n₂ : ℕ) = n₁+n₂ := rfl
    rw [Nat.cast_add]
    field_simp
    <;> ring
  have hleftNE : Nonempty (Fin n₁ × Fin n₁) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hrightNE : Nonempty (Fin n₂ × Fin n₂) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  letI : Nonempty (Fin n₁ × Fin n₁) := hleftNE
  letI : Nonempty (Fin n₂ × Fin n₂) := hrightNE
  let L : ℝ := uniformMean (fun xy : Fin n₁ × Fin n₁ =>
    f (addEdge G s(leftVertex n₁ n₂ xy.1, leftVertex n₁ n₂ xy.2)))
  let R : ℝ := uniformMean (fun xy : Fin n₂ × Fin n₂ =>
    f (addEdge G s(rightVertex n₁ n₂ xy.1, rightVertex n₁ n₂ xy.2)))
  have hl : 0 ≤ L ∧ L ≤ 1 := by
    dsimp [L]
    exact uniformMean_bounds _ (fun xy => h0 _) (fun xy => h1 _)
  have hr : 0 ≤ R ∧ R ≤ 1 := by
    dsimp [R]
    exact uniformMean_bounds _ (fun xy => h0 _) (fun xy => h1 _)
  unfold localStep
  change 0 ≤ (n₁ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) * L +
      (n₂ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) * R ∧
    (n₁ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) * L +
      (n₂ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) * R ≤ 1
  constructor
  · exact add_nonneg (mul_nonneg hA hl.1) (mul_nonneg hB hr.1)
  · calc
      (n₁ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) * L +
        (n₂ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) * R
          ≤ (n₁ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) * 1 +
        (n₂ : ℝ) / ((n₁+n₂ : ℕ) : ℝ) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hl.2 hA) (mul_le_mul_of_nonneg_left hr.2 hB)
      _ = 1 := by rw [mul_one, mul_one, hsum]

private lemma indicator_bounds {V : Type} (q : ℕ) (G : MGraph V) :
    0 ≤ indicator (Colorable q G) ∧ indicator (Colorable q G) ≤ 1 := by
  by_cases h : Colorable q G <;> simp [indicator, h]

private lemma globalIterate_bounds (n₁ n₂ q m : ℕ) (hn : 1 ≤ n₁+n₂)
    (G : MGraph (Fin (n₁+n₂))) :
    0 ≤ ((globalStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) G ∧
    ((globalStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) G ≤ 1 := by
  have hn' : 0 < n₁+n₂ := by omega
  have hnR : 0 < ((n₁+n₂ : ℕ) : ℝ) := by exact_mod_cast hn'
  induction m generalizing G with
  | zero => simpa using indicator_bounds q G
  | succ m ih =>
      simpa [Function.iterate_succ_apply'] using
        globalStep_bounds n₁ n₂ _ hnR
          (fun H => (ih H).1) (fun H => (ih H).2) G

private lemma localIterate_bounds (n₁ n₂ q m : ℕ) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (G : MGraph (Fin (n₁+n₂))) :
    0 ≤ ((localStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) G ∧
    ((localStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) G ≤ 1 := by
  induction m generalizing G with
  | zero => simpa using indicator_bounds q G
  | succ m ih =>
      simpa [Function.iterate_succ_apply'] using
        localStep_bounds n₁ n₂ hn₁ hn₂ _ (fun H => (ih H).1) (fun H => (ih H).2) G

private lemma summable_mul_unitBound (w a : ℕ → ℝ) (hw : Summable w)
    (hw0 : ∀ m, 0 ≤ w m) (ha0 : ∀ m, 0 ≤ a m) (ha1 : ∀ m, a m ≤ 1) :
    Summable (fun m => w m * a m) := by
  have hbound : Summable (fun m => w m * 1) := by simpa using hw
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (hw0 m) (ha0 m))
    (fun m => mul_le_mul_of_nonneg_left (ha1 m) (hw0 m)) hbound

/-- The leaf assembled from the Poisson normalization and its two graph-law
identifications. -/
theorem SA_R70bStatement_of_mixture_identities
    (hP : ThresholdFoundations.PrePoissonStatement.{0})
    (hG : ThLean.Contrib.SA51.GlobalPoissonMixtureIdentityStatement)
    (hL : ThLean.Contrib.SA51.LocalPoissonMixtureIdentityStatement) :
    ThLean.BP.SA.SA_R70bStatement := by
  intro q n₁ n₂ hq hn₁ hn₂ c hc
  let z : ℝ := c * (n₁+n₂ : ℕ)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  obtain ⟨hw, _, hw0⟩ := hP.1 z hz
  have hsumG : Summable (fun m : ℕ => poissonWeight z m *
      ((globalStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0) := by
    apply summable_mul_unitBound (poissonWeight z) _ hw hw0
    · intro m
      exact (globalIterate_bounds n₁ n₂ q m (by omega) 0).1
    · intro m
      exact (globalIterate_bounds n₁ n₂ q m (by omega) 0).2
  have hsumL : Summable (fun m : ℕ => poissonWeight z m *
      ((localStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0) := by
    apply summable_mul_unitBound (poissonWeight z) _ hw hw0
    · intro m
      exact (localIterate_bounds n₁ n₂ q m hn₁ hn₂ 0).1
    · intro m
      exact (localIterate_bounds n₁ n₂ q m hn₁ hn₂ 0).2
  have hG' := hG q n₁ n₂ hq hn₁ hn₂ c hc
  have hL' := hL q n₁ n₂ hq hn₁ hn₂ c hc
  refine ⟨?_, hsumG, hsumL, ?_, ?_⟩
  · intro m
    exact hw0 m
  · simpa [z] using hG'
  · simpa [z] using hL'

end ThLean.W.SA51

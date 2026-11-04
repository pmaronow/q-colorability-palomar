module

public import ThLean.W.SA27S.SignedWeights

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA27S
open ThresholdFoundations ThLean.BP.SA

variable {A B C X Y : Type}

lemma productWeight_summable {a : A → ℝ} {b : B → ℝ}
    (ha : Summable a) (hb : Summable b) :
    Summable (fun p : A × B => a p.1 * b p.2) :=
  summable_mul_of_summable_norm ha.norm hb.norm

lemma productWeight_tsum {a : A → ℝ} {b : B → ℝ}
    (ha : Summable a) (hb : Summable b) :
    (∑' p : A × B, a p.1 * b p.2) = (∑' x, a x) * (∑' y, b y) :=
  (tsum_mul_tsum_of_summable_norm ha.norm hb.norm).symm

lemma productWeight_fiber {a : A → ℝ} {b : B → ℝ}
    (ha : Summable a) (hb : Summable b) (g : A → X) (h : B → Y)
    (x : X) (y : Y) :
    (∑' p : {p : A × B // (g p.1, h p.2) = (x, y)}, a p.val.1 * b p.val.2) =
      (∑' p : {p // g p = x}, a p.val) * (∑' p : {p // h p = y}, b p.val) := by
  rw [fiber_tsum_eq_indicator (fun p : A × B => a p.1 * b p.2)
    (fun p => (g p.1, h p.2)) (x, y),
    fiber_tsum_eq_indicator a g x, fiber_tsum_eq_indicator b h y]
  have ha' := summable_weighted ha (fun p => indicator (g p = x))
    (fun _ => indicator_norm_le _)
  have hb' := summable_weighted hb (fun p => indicator (h p = y))
    (fun _ => indicator_norm_le _)
  rw [← productWeight_tsum ha' hb']
  apply tsum_congr
  intro p
  by_cases hg : g p.1 = x <;> by_cases hh : h p.2 = y <;>
    simp [indicator, Prod.mk.injEq, hg, hh]

def tripleWeight (a : A → ℝ) (b : B → ℝ) (c : C → ℝ) (p : A × (B × C)) : ℝ :=
  a p.1 * (b p.2.1 * c p.2.2)

lemma tripleWeight_summable {a : A → ℝ} {b : B → ℝ} {c : C → ℝ}
    (ha : Summable a) (hb : Summable b) (hc : Summable c) :
    Summable (tripleWeight a b c) :=
  productWeight_summable ha (productWeight_summable hb hc)

abbrev TriplePrefix (A B C : Type) := Prefix A × (Prefix B × Prefix C)
abbrev TripleCounts (A B C : Type) := (A → ℕ) × ((B → ℕ) × (C → ℕ))

def tripleHistogram [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (p : TriplePrefix A B C) : TripleCounts A B C :=
  (histogram p.1, histogram p.2.1, histogram p.2.2)

def countWeight (D : Type) [Fintype D] (μ : ℝ) (z : D → ℕ) : ℝ :=
  ∏ d, poissonWeight (μ / (Fintype.card D : ℝ)) (z d)

lemma tripleHistogram_fiber (h11a : SA_I11aStatement)
    (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (μ : Fin 3 → ℝ) (z : TripleCounts A B C) :
    (∑' p : {p : TriplePrefix A B C // tripleHistogram p = z},
      tripleWeight (prefixWeight A (μ 0)) (prefixWeight B (μ 1))
        (prefixWeight C (μ 2)) p.val) =
      tripleWeight (countWeight A (μ 0)) (countWeight B (μ 1))
        (countWeight C (μ 2)) z := by
  rcases z with ⟨x, y, z⟩
  change (∑' p : {p : TriplePrefix A B C //
      (histogram p.1, (histogram p.2.1, histogram p.2.2)) = (x, (y, z))},
    prefixWeight A (μ 0) p.val.1 *
      (prefixWeight B (μ 1) p.val.2.1 * prefixWeight C (μ 2) p.val.2.2)) = _
  rw [productWeight_fiber (prefixWeight_summable A (μ 0))
    (productWeight_summable (prefixWeight_summable B (μ 1))
      (prefixWeight_summable C (μ 2))) histogram
      (fun p => (histogram p.1, histogram p.2)) x (y, z)]
  rw [productWeight_fiber (prefixWeight_summable B (μ 1))
    (prefixWeight_summable C (μ 2)) histogram histogram y z]
  simp only [prefixWeight_histogram h11a, tripleWeight, countWeight]

lemma tripleHistogram_mean (h11a : SA_I11aStatement)
    (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (μ : Fin 3 → ℝ) (F : TripleCounts A B C → ℝ) (hF : ∀ z, ‖F z‖ ≤ 1) :
    (∑' p : TriplePrefix A B C,
      tripleWeight (prefixWeight A (μ 0)) (prefixWeight B (μ 1))
        (prefixWeight C (μ 2)) p * F (tripleHistogram p)) =
    ∑' z : TripleCounts A B C,
      tripleWeight (countWeight A (μ 0)) (countWeight B (μ 1))
        (countWeight C (μ 2)) z * F z := by
  exact tsum_pushforward
    (tripleWeight_summable (prefixWeight_summable A (μ 0))
      (prefixWeight_summable B (μ 1)) (prefixWeight_summable C (μ 2)))
    tripleHistogram _ (tripleHistogram_fiber h11a A B C μ) F hF

end ThLean.W.SA27S

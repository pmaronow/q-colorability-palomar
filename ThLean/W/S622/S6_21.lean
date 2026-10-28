import ThLean.BP.S6.Credit

noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S622

private theorem low_degree_term_bound (d c : ℕ) (hc : 1 ≤ c) (hd : d < c) :
    (d : ℝ) ≤ 2 * ((c : ℝ) - 1) * min ((d : ℝ) / (c : ℝ)) 1 := by
  by_cases hc1 : c = 1
  · subst c
    have hd0 : d = 0 := by omega
    simp [hd0]
  · have hc2 : 2 ≤ c := by omega
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hc)
    have hdc : (d : ℝ) < (c : ℝ) := by exact_mod_cast hd
    have hratio : (d : ℝ) / (c : ℝ) ≤ 1 := (div_le_one₀ hcpos).2 (le_of_lt hdc)
    rw [min_eq_left hratio]
    calc
      (d : ℝ) ≤ (2 * ((c : ℝ) - 1) * (d : ℝ)) / (c : ℝ) := by
        apply (le_div_iff₀ hcpos).2
        have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
        have hcminus : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc2
        nlinarith [mul_nonneg hdnonneg (sub_nonneg.mpr hcminus)]
      _ = 2 * ((c : ℝ) - 1) * ((d : ℝ) / (c : ℝ)) := by ring

private theorem small_pairs_card_le_sum_low {V : Type} [Fintype V]
    (R : Finset (V × V)) (c : ℕ) :
    ((R \ largePart R c).card : ℝ) ≤
      ∑ a ∈ Finset.univ.filter (fun a : V => (sectionOf R a).card < c),
        ((sectionOf R a).card : ℝ) := by
  classical
  let low : Finset V := Finset.univ.filter (fun a : V => (sectionOf R a).card < c)
  let cover : Finset (V × V) := low.biUnion (fun a => {a} ×ˢ sectionOf R a)
  have hsub : R \ largePart R c ⊆ cover := by
    intro ab hab
    rcases Finset.mem_sdiff.mp hab with ⟨habR, habNotLarge⟩
    rcases ab with ⟨a, b⟩
    have habNotLarge' : ¬ c ≤ max (sectionOf R a).card (sectionOf R b).card := by
      simpa [largePart, habR] using habNotLarge
    have hmax : max (sectionOf R a).card (sectionOf R b).card < c :=
      Nat.lt_of_not_ge habNotLarge'
    have hlow : (sectionOf R a).card < c :=
      lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hbSec : b ∈ sectionOf R a := by
      rw [sectionOf, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, habR⟩
    change (a, b) ∈ cover
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlow⟩, ?_⟩
    simp [hbSec]
  have hcover : cover.card ≤ ∑ a ∈ low, ({a} ×ˢ sectionOf R a).card := by
    exact Finset.card_biUnion_le
  have hcover' : cover.card ≤ ∑ a ∈ low, (sectionOf R a).card := by
    simpa [Finset.card_product] using hcover
  have hcard : (R \ largePart R c).card ≤ ∑ a ∈ low, (sectionOf R a).card :=
    (Finset.card_le_card hsub).trans hcover'
  exact_mod_cast hcard

private theorem small_pairs_bound {V : Type} [Fintype V]
    (R : Finset (V × V)) (c : ℕ) (hc : 1 ≤ c) :
    ((R \ largePart R c).card : ℝ) ≤
      2 * ((c : ℝ) - 1) * sectionMass R c := by
  classical
  let low : Finset V := Finset.univ.filter (fun a : V => (sectionOf R a).card < c)
  have hcard := small_pairs_card_le_sum_low R c
  have hterms : ∀ a ∈ low,
      ((sectionOf R a).card : ℝ) ≤
        2 * ((c : ℝ) - 1) * min (((sectionOf R a).card : ℝ) / (c : ℝ)) 1 := by
    intro a ha
    exact low_degree_term_bound _ _ hc (Finset.mem_filter.mp ha).2
  have hsum : (∑ a ∈ low, ((sectionOf R a).card : ℝ)) ≤
      ∑ a ∈ low,
        2 * ((c : ℝ) - 1) * min (((sectionOf R a).card : ℝ) / (c : ℝ)) 1 :=
    Finset.sum_le_sum hterms
  have hsum' : (∑ a ∈ low, ((sectionOf R a).card : ℝ)) ≤
      2 * ((c : ℝ) - 1) * sectionMass R c := by
    have hcReal : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    have hcoeff : 0 ≤ 2 * ((c : ℝ) - 1) := by nlinarith
    calc
      _ ≤ ∑ a ∈ low,
          2 * ((c : ℝ) - 1) * min (((sectionOf R a).card : ℝ) / (c : ℝ)) 1 := hsum
      _ = 2 * ((c : ℝ) - 1) *
          (∑ a ∈ low, min (((sectionOf R a).card : ℝ) / (c : ℝ)) 1) := by
            rw [← Finset.mul_sum]
      _ ≤ 2 * ((c : ℝ) - 1) *
          (∑ a : V, min (((sectionOf R a).card : ℝ) / (c : ℝ)) 1) := by
            apply mul_le_mul_of_nonneg_left _ hcoeff
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ low)
              (by intro a ha hnot; positivity)
      _ = 2 * ((c : ℝ) - 1) * sectionMass R c := by rfl
  exact hcard.trans hsum'

/-- The leaf follows from the preceding large-section estimate S6_20. -/
theorem S6_21Statement_of_deps (h20 : S6_20Statement) : S6_21Statement := by
  intro V inst R c hc hsym
  have hsmall := small_pairs_bound R c hc
  have h20R := h20 V R c hc hsym
  have hlarge : ((largePart R c).card : ℝ) ≤ 2 * commonMass R c := h20R.2
  have hlargeSub : largePart R c ⊆ R := by
    intro ab hab
    exact (Finset.mem_filter.mp hab).1
  have hsplitNat : (R \ largePart R c).card + (R ∩ largePart R c).card = R.card :=
    Finset.card_sdiff_add_card_inter R (largePart R c)
  have hinter : R ∩ largePart R c = largePart R c :=
    Finset.inter_eq_right.mpr hlargeSub
  have hsplit : (R.card : ℝ) = ((R \ largePart R c).card : ℝ) +
      ((largePart R c).card : ℝ) := by
    exact_mod_cast (by simpa [hinter] using hsplitNat.symm)
  refine ⟨hsmall, ?_⟩
  rw [hsplit]
  nlinarith [hsmall, hlarge]

end ThLean.W.S622

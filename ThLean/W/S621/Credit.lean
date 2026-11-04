module

public import ThLean.BP.S6.Credit

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S621

private lemma sum_pairs_sections {V : Type} [Fintype V]
    (R : Finset (V × V)) (f : V × V → ℝ) :
    (∑ p ∈ R, f p) = ∑ a : V, ∑ b ∈ sectionOf R a, f (a, b) := by
  classical
  have hR : R = (Finset.univ ×ˢ Finset.univ).filter (fun p => p ∈ R) := by
    ext p
    simp
  calc
    (∑ p ∈ R, f p) = ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p => p ∈ R), f p := by
      exact congrArg (fun s : Finset (V × V) => ∑ p ∈ s, f p) hR
    _ = ∑ p ∈ Finset.univ ×ˢ Finset.univ, if p ∈ R then f p else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ a ∈ Finset.univ, ∑ b ∈ Finset.univ,
        if (a, b) ∈ R then f (a, b) else 0 := by
      rw [Finset.sum_product]
    _ = ∑ a : V, ∑ b : V, if (a, b) ∈ R then f (a, b) else 0 := by simp
    _ = ∑ a : V, ∑ b ∈ sectionOf R a, f (a, b) := by
      simp [sectionOf, Finset.sum_filter]

private lemma sum_pair_swap {V : Type} [Fintype V]
    (R : Finset (V × V)) (hR : SymmetricRelation R) (f : V × V → ℝ) :
    (∑ p ∈ R, f p) = ∑ p ∈ R, f p.swap := by
  classical
  refine Finset.sum_bij' (s := R) (t := R) (f := f) (g := fun p => f p.swap)
    (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact (hR p.1 p.2).mp hp
  · intro p hp
    exact (hR p.1 p.2).mp hp
  · intro p hp
    rfl
  · intro p hp
    simp
  · intro p hp
    rfl

/-- P4-HIGH-20, proved using the preceding reciprocal double-counting node. -/
theorem S6_20Statement_of_deps (h19 : S6_19Statement) : S6_20Statement := by
  classical
  intro V _ R c hc hR
  let f (p : V × V) : ℝ :=
    ((sectionOf R p.1).card : ℝ) / max (c : ℝ) ((sectionOf R p.2).card : ℝ)
  let g (p : V × V) : ℝ := f p + f p.swap
  let P : ℝ := ∑ a : V, ∑ b ∈ sectionOf R a,
    ((sectionOf R a).card : ℝ) / max (c : ℝ) ((sectionOf R b).card : ℝ)

  have hPedge : (∑ p ∈ R, f p) = P := by
    rw [sum_pairs_sections]

  have hswap := sum_pair_swap R hR f
  have hQedge : (∑ p ∈ R, f p.swap) = P := by
    calc
      (∑ p ∈ R, f p.swap) = ∑ p ∈ R, f p := hswap.symm
      _ = P := hPedge

  have hT := (h19 V R c hc hR).2
  let T : ℝ := ∑ y : V, ∑ a ∈ sectionOf R y, ∑ b ∈ sectionOf R y,
    1 / max (c : ℝ) ((sectionOf R a ∩ sectionOf R b).card : ℝ)

  have hPexpand : P = ∑ y : V, ∑ a ∈ sectionOf R y, ∑ b ∈ sectionOf R y,
      1 / max (c : ℝ) ((sectionOf R a).card : ℝ) := by
    simp only [P]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_const]
    simp [nsmul_eq_mul, div_eq_mul_inv]

  have hPleT : P ≤ T := by
    change P ≤ ∑ y : V, ∑ a ∈ sectionOf R y, ∑ b ∈ sectionOf R y,
      1 / max (c : ℝ) ((sectionOf R a ∩ sectionOf R b).card : ℝ)
    rw [hPexpand]
    apply Finset.sum_le_sum
    intro y _
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    have hsub : sectionOf R a ∩ sectionOf R b ⊆ sectionOf R a := Finset.inter_subset_left
    have hcard : (sectionOf R a ∩ sectionOf R b).card ≤ (sectionOf R a).card :=
      Finset.card_le_card hsub
    have hden :
        max (c : ℝ) ((sectionOf R a ∩ sectionOf R b).card : ℝ) ≤
          max (c : ℝ) ((sectionOf R a).card : ℝ) := by
      apply max_le_max le_rfl
      exact_mod_cast hcard
    apply one_div_le_one_div_of_le (by positivity) hden

  have hPcommon : P ≤ commonMass R c := by
    rw [hT]
    exact hPleT

  have hfirst : (∑ p ∈ R, f p) ≤ commonMass R c := by
    rw [hPedge]
    exact hPcommon

  have hsecond : (∑ p ∈ R, f p.swap) ≤ commonMass R c := by
    rw [hQedge]
    exact hPcommon

  have hsum : (∑ p ∈ R, g p) ≤ 2 * commonMass R c := by
    simp only [g, Finset.sum_add_distrib]
    linarith

  have hlarge : ((largePart R c).card : ℝ) ≤ ∑ p ∈ R, g p := by
    have hsub : largePart R c ⊆ R := Finset.filter_subset _ _
    have hcard : ((largePart R c).card : ℝ) =
        ∑ p ∈ R, if p ∈ largePart R c then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      have hf : R.filter (fun p => p ∈ largePart R c) = largePart R c := by
        ext p
        simp [hsub]
      rw [hf]
      simp
    rw [hcard]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hLp : p ∈ largePart R c
    · simp only [if_pos hLp]
      have hthreshold :
          c ≤ max (sectionOf R p.1).card (sectionOf R p.2).card :=
        (Finset.mem_filter.mp hLp).2
      by_cases horder : (sectionOf R p.2).card ≤ (sectionOf R p.1).card
      · have hcA : c ≤ (sectionOf R p.1).card := by
          simpa [Nat.max_eq_left horder] using hthreshold
        have hcA' : (c : ℝ) ≤ (sectionOf R p.1).card := by exact_mod_cast hcA
        have hBA : (sectionOf R p.2).card ≤ (sectionOf R p.1).card := horder
        have hBA' : ((sectionOf R p.2).card : ℝ) ≤ (sectionOf R p.1).card := by
          exact_mod_cast hBA
        have hden : max (c : ℝ) ((sectionOf R p.2).card : ℝ) ≤
            (sectionOf R p.1).card := max_le_iff.mpr ⟨hcA', hBA'⟩
        have hdenpos : 0 < max (c : ℝ) ((sectionOf R p.2).card : ℝ) := by positivity
        have hratio : 1 ≤ f p := by
          dsimp [f]
          apply (le_div_iff₀ hdenpos).2
          nlinarith
        dsimp [g]
        have : 0 ≤ f p.swap := by dsimp [f]; positivity
        linarith
      · have horder' : (sectionOf R p.1).card ≤ (sectionOf R p.2).card := Nat.le_of_not_ge horder
        have hcB : c ≤ (sectionOf R p.2).card := by
          simpa [Nat.max_eq_right horder'] using hthreshold
        have hcB' : (c : ℝ) ≤ (sectionOf R p.2).card := by exact_mod_cast hcB
        have hAB' : ((sectionOf R p.1).card : ℝ) ≤ (sectionOf R p.2).card := by
          exact_mod_cast horder'
        have hden : max (c : ℝ) ((sectionOf R p.1).card : ℝ) ≤
            (sectionOf R p.2).card := max_le_iff.mpr ⟨hcB', hAB'⟩
        have hdenpos : 0 < max (c : ℝ) ((sectionOf R p.1).card : ℝ) := by positivity
        have hratio : 1 ≤ f p.swap := by
          dsimp [f]
          apply (le_div_iff₀ hdenpos).2
          nlinarith
        dsimp [g]
        have : 0 ≤ f p := by dsimp [f]; positivity
        linarith
    · simp only [if_neg hLp]
      dsimp [g, f]
      positivity

  refine ⟨?_, ?_⟩
  · calc
      (∑ p ∈ R, (f p + f p.swap)) = (∑ p ∈ R, f p) + (∑ p ∈ R, f p.swap) :=
        Finset.sum_add_distrib
      _ ≤ commonMass R c + commonMass R c := add_le_add hfirst hsecond
      _ = 2 * commonMass R c := by ring
  · exact hlarge.trans hsum

end ThLean.W.S621

module

public import ThLean.BP.S6.Credit

@[expose] public section

open scoped BigOperators
open ThLean.BP.S6

namespace ThLean.W.S620

private theorem min_div_one_eq_section_sum {V : Type} [Fintype V]
    (s : Finset V) (c : ℕ) (hc : 1 ≤ c) :
    min ((s.card : ℝ) / c) 1 =
      ∑ _y ∈ s, 1 / max (c : ℝ) (s.card : ℝ) := by
  classical
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hc)
  by_cases hsc : s.card ≤ c
  · have hscR : (s.card : ℝ) ≤ (c : ℝ) := by exact_mod_cast hsc
    rw [min_eq_left ((div_le_one₀ hcpos).2 hscR), max_eq_left hscR]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  · have hcs : c ≤ s.card := Nat.le_of_not_ge hsc
    have hcsR : (c : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcs
    have hspos : (0 : ℝ) < (s.card : ℝ) := lt_of_lt_of_le hcpos hcsR
    rw [min_eq_right ((one_le_div₀ hcpos).2 hcsR), max_eq_right hcsR]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp

theorem S6_19Statement_holds : ThLean.BP.S6.S6_19Statement := by
  classical
  intro V _ R c hc hR
  constructor
  · intro a b
    exact min_div_one_eq_section_sum (sectionOf R a ∩ sectionOf R b) c hc
  · unfold commonMass
    let K : V → V → ℝ := fun a b =>
      1 / max (c : ℝ) ((sectionOf R a ∩ sectionOf R b).card : ℝ)
    have hpair (a b : V) :
        min (((sectionOf R a ∩ sectionOf R b).card : ℝ) / c) 1 =
          ∑ _y ∈ sectionOf R a ∩ sectionOf R b, K a b := by
      simpa [K] using
        min_div_one_eq_section_sum (sectionOf R a ∩ sectionOf R b) c hc
    have hleft :
        (∑ a : V, ∑ b : V,
          ∑ y ∈ sectionOf R a ∩ sectionOf R b, K a b) =
        ∑ a : V, ∑ b : V, ∑ y : V,
          if (a, y) ∈ R ∧ (b, y) ∈ R then K a b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      have hs : sectionOf R a ∩ sectionOf R b =
          Finset.univ.filter (fun y : V => (a, y) ∈ R ∧ (b, y) ∈ R) := by
        ext y
        simp [sectionOf]
      rw [hs, Finset.sum_filter]
    have hright :
        (∑ y : V, ∑ a ∈ sectionOf R y, ∑ b ∈ sectionOf R y, K a b) =
        ∑ y : V, ∑ a : V, if (y, a) ∈ R then
          ∑ b : V, if (y, b) ∈ R then K a b else 0 else 0 := by
      simp [sectionOf, Finset.sum_filter]
    have hbody (y a : V) :
        (∑ b : V, if (a, y) ∈ R ∧ (b, y) ∈ R then K a b else 0) =
          if (y, a) ∈ R then
            ∑ b : V, if (y, b) ∈ R then K a b else 0 else 0 := by
      by_cases hay : (a, y) ∈ R
      · have hya : (y, a) ∈ R := (hR a y).mp hay
        simp [hay, hya]
        apply Finset.sum_congr rfl
        intro b _
        simp [hR b y]
      · have hya : (y, a) ∉ R := fun h => hay ((hR a y).mpr h)
        simp [hay, hya]
    have hswap :
        (∑ a : V, ∑ b : V, ∑ y : V,
          if (a, y) ∈ R ∧ (b, y) ∈ R then K a b else 0) =
        ∑ y : V, ∑ a : V, if (y, a) ∈ R then
          ∑ b : V, if (y, b) ∈ R then K a b else 0 else 0 := by
      calc
        _ = ∑ a : V, ∑ y : V, ∑ b : V,
            if (a, y) ∈ R ∧ (b, y) ∈ R then K a b else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = ∑ y : V, ∑ a : V, ∑ b : V,
            if (a, y) ∈ R ∧ (b, y) ∈ R then K a b else 0 := by
          exact Finset.sum_comm
        _ = ∑ y : V, ∑ a : V, if (y, a) ∈ R then
            ∑ b : V, if (y, b) ∈ R then K a b else 0 else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro a _
          exact hbody y a
    calc
      (∑ a : V, ∑ b : V,
        min (((sectionOf R a ∩ sectionOf R b).card : ℝ) / c) 1) =
          ∑ a : V, ∑ b : V,
            ∑ y ∈ sectionOf R a ∩ sectionOf R b, K a b := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact hpair a b
      _ = ∑ a : V, ∑ b : V, ∑ y : V,
          if (a, y) ∈ R ∧ (b, y) ∈ R then K a b else 0 := hleft
      _ = ∑ y : V, ∑ a : V, if (y, a) ∈ R then
          ∑ b : V, if (y, b) ∈ R then K a b else 0 else 0 := hswap
      _ = ∑ y : V, ∑ a ∈ sectionOf R y, ∑ b ∈ sectionOf R y, K a b :=
          hright.symm

end ThLean.W.S620

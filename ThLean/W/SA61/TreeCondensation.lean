module

public import ThLean.BP.SA.Tree

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA61

open ThLean.BP.SA

private lemma log_four_thirds_ge_quarter :
    (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (4 / 3 : ℝ))
  norm_num at h
  exact h

private lemma log_four_thirds_le_third :
    Real.log (4 / 3 : ℝ) ≤ (1 / 3 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (4 / 3 : ℝ))
  norm_num at h
  exact h

private lemma path_grid_le {K i : ℕ} {ℓ : ℝ}
    (hℓ : 4 * Real.exp K ≤ ℓ) :
    Real.exp ((K + i / 4 : ℕ) : ℝ) ≤ ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1) := by
  have hlog := log_four_thirds_ge_quarter
  have hi : (i : ℝ) / 4 ≤ ((i + 1 : ℕ) : ℝ) * Real.log (4 / 3 : ℝ) := by
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hprod := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) by positivity)
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_cast
    rw [hcast] at hprod
    nlinarith [hprod]
  have hdiv : ((i / 4 : ℕ) : ℝ) ≤ (i : ℝ) / 4 := Nat.cast_div_le
  have hpow : Real.exp ((i + 1 : ℕ) * Real.log (4 / 3 : ℝ)) =
      (4 / 3 : ℝ) ^ (i + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : 0 < (4 / 3 : ℝ))]
  have hexp : Real.exp ((i / 4 : ℕ) : ℝ) ≤ (4 / 3 : ℝ) ^ (i + 1) := by
    rw [← hpow]
    exact Real.exp_le_exp.mpr (hdiv.trans hi)
  have hscale : Real.exp (K : ℝ) ≤ ℓ / 4 := by
    nlinarith
  calc
    Real.exp ((K + i / 4 : ℕ) : ℝ) =
        Real.exp (K : ℝ) * Real.exp ((i / 4 : ℕ) : ℝ) := by
          rw [Nat.cast_add, Real.exp_add]
    _ ≤ Real.exp (K : ℝ) * (4 / 3 : ℝ) ^ (i + 1) :=
          mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg _)
    _ ≤ ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1) :=
          mul_le_mul_of_nonneg_right hscale (by positivity)

private lemma sum_div_four_le_tsum (f : ℕ → ℝ) (m : ℕ)
    (hf : ∀ k, 0 ≤ f k) (hs : Summable f) :
    (∑ i ∈ Finset.range m, f (i / 4)) ≤ 4 * ∑' k, f k := by
  classical
  let e : ℕ → ℕ × ℕ := fun i => (i / 4, i % 4)
  let t : Finset (ℕ × ℕ) := Finset.range m ×ˢ Finset.range 4
  have he : Set.InjOn e (Finset.range m) := by
    intro i hi j hj hij
    have hdiv : i / 4 = j / 4 := congrArg Prod.fst hij
    have hmod : i % 4 = j % 4 := congrArg Prod.snd hij
    omega
  have hsub : (Finset.range m).image e ⊆ t := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    simp only [t, Finset.mem_product, Finset.mem_range, e]
    exact ⟨lt_of_le_of_lt (Nat.div_le_self i 4) (Finset.mem_range.mp hi), Nat.mod_lt i (by decide)⟩
  have hpair := Finset.sum_le_sum_of_injOn (f := fun i => f (i / 4))
      (g := fun p : ℕ × ℕ => f p.1) e he hsub (by intro i hi; rfl)
      (by intro p hp hnot; exact hf p.1)
  calc
    (∑ i ∈ Finset.range m, f (i / 4)) ≤ ∑ p ∈ t, f p.1 := hpair
    _ = 4 * ∑ k ∈ Finset.range m, f k := by
      simp [t, Finset.sum_product, Finset.sum_const, ← Finset.mul_sum]
    _ ≤ 4 * ∑' k, f k := by
      exact mul_le_mul_of_nonneg_left (hs.sum_le_tsum (Finset.range m) (fun k _ => hf k))
        (by norm_num)

private lemma grid_summable (u₀ : ℝ) (g : ℝ → ℝ) (K : ℕ)
    (ha : AnalyticError u₀ g) :
    Summable (fun k : ℕ => g (Real.exp ((K + k : ℕ) : ℝ))) := by
  rcases ha with ⟨_, _, _, hbase⟩
  apply (summable_nat_add_iff 1).1
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_assoc] using
    (summable_nat_add_iff K).2 hbase

theorem SA_T35Statement_holds : ThLean.BP.SA.SA_T35Statement := by
  intro u₀ g ha K hu₀ ℓ hℓ m
  rcases ha with ⟨hu₀one, hg_nonneg, hg_anti, hbase⟩
  let grid : ℕ → ℝ := fun k => g (Real.exp ((K + k : ℕ) : ℝ))
  have hgrid_nonneg : ∀ k, 0 ≤ grid k := by
    intro k
    apply hg_nonneg
    have harg : (0 : ℝ) ≤ ((K + k : ℕ) : ℝ) := Nat.cast_nonneg _
    have h := Real.add_one_le_exp ((K + k : ℕ) : ℝ)
    nlinarith [h]
  have hgrid_sum : Summable grid := by
    simpa [grid] using grid_summable u₀ g K ⟨hu₀one, hg_nonneg, hg_anti, hbase⟩
  have hpath : ∀ i ∈ Finset.range m,
      g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1)) ≤ grid (i / 4) := by
    intro i hi
    apply hg_anti
    · exact Set.mem_Ici.mpr (le_trans hu₀ (by
        apply Real.exp_le_exp.mpr
        exact_mod_cast (Nat.le_add_right K (i / 4))))
    · exact Set.mem_Ici.mpr (le_trans hu₀ (by
        have hbasegrid : Real.exp K ≤ Real.exp ((K + i / 4 : ℕ) : ℝ) := by
          apply Real.exp_le_exp.mpr
          exact_mod_cast (Nat.le_add_right K (i / 4))
        exact hbasegrid.trans (path_grid_le hℓ)))
    · exact path_grid_le hℓ
  have hfinite :
      (∑ i ∈ Finset.range m, g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1))) ≤
        4 * ∑' k, grid k := by
    calc
      _ ≤ ∑ i ∈ Finset.range m, grid (i / 4) := Finset.sum_le_sum hpath
      _ ≤ 4 * ∑' k, grid k := sum_div_four_le_tsum grid m hgrid_nonneg hgrid_sum
  have hlogpos : 0 < Real.log (4 / 3 : ℝ) := by
    linarith [log_four_thirds_ge_quarter]
  have hrecip : (3 : ℝ) ≤ 1 / Real.log (4 / 3 : ℝ) := by
    apply (le_div_iff₀ hlogpos).2
    nlinarith [log_four_thirds_le_third]
  have hceil : 3 ≤ Nat.ceil (1 / Real.log (4 / 3 : ℝ)) := by
    have hreal : (3 : ℝ) ≤ (Nat.ceil (1 / Real.log (4 / 3 : ℝ)) : ℝ) :=
      hrecip.trans (Nat.le_ceil _)
    exact_mod_cast hreal
  have hconstNat : 4 ≤ Nat.ceil (1 / Real.log (4 / 3 : ℝ)) + 1 := by omega
  have hconst : (4 : ℝ) ≤
      ((Nat.ceil (1 / Real.log (4 / 3 : ℝ)) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hconstNat
  have htsum_nonneg : 0 ≤ ∑' k, grid k := tsum_nonneg hgrid_nonneg
  calc
    (∑ i ∈ Finset.range m, g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1))) ≤
        4 * ∑' k, grid k := hfinite
    _ ≤ ((Nat.ceil (1 / Real.log (4 / 3 : ℝ)) + 1 : ℕ) : ℝ) * ∑' k, grid k :=
        mul_le_mul_of_nonneg_right hconst htsum_nonneg

end ThLean.W.SA61

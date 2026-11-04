module

public import ThLean.BP.S3.Lifetime

@[expose] public section

/-! P1-26 follows from the exponential survival tail and its summation bound. -/

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S328
open ThresholdFoundations
universe u

theorem S3_26Statement_of_deps
    (h24 : ThLean.BP.S3.S3_24Statement.{u})
    (h25 : ThLean.BP.S3.S3_25Statement) :
    ThLean.BP.S3.S3_26Statement.{u} := by
  intro V _ q hq hV
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hVge : 2 ≤ Fintype.card V := by omega
  have hN : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast (show 2 ≤ Fintype.card V by omega)
  have hsurv_nonneg (G : MGraph V) (k : ℕ) : 0 ≤ survival q G k := by
    unfold survival uniformProb uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x hx
      unfold indicator
      split <;> norm_num
    · positivity
  let B : ℝ := (q : ℝ) ^ Fintype.card V
  let a : ℝ := 1 / (2 * (q : ℝ))
  let majorant : ℕ → ℝ := fun k => min 1 (B * Real.exp (-a * (k : ℝ)))
  have hB : 1 ≤ B := by
    dsimp [B]
    exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ (q : ℝ))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hMajSummable : Summable majorant := by
    simpa [majorant, B, a, div_eq_mul_inv, mul_comm] using
      (h25 B a hB ha).1
  have hdom (G : MGraph V) (k : ℕ) : survival q G k ≤ majorant k := by
    have hexp : -(k : ℝ) / (2 * (q : ℝ)) = -a * (k : ℝ) := by
      dsimp [a]
      field_simp
    simpa [majorant, B, hexp] using
      ((h24 V q hq hVge G k).2.1 hV)
  have hsurv_summable (G : MGraph V) : Summable (fun k => survival q G k) := by
    exact hMajSummable.of_nonneg_of_le (fun k => hsurv_nonneg G k) (hdom G)
  have hsum_bound (G : MGraph V) :
      (∑' k : ℕ, survival q G k) ≤
        2 * (q : ℝ) * Fintype.card V * Real.log (q : ℝ) + 2 * q + 2 := by
    have hle : (∑' k : ℕ, survival q G k) ≤ ∑' k : ℕ, majorant k :=
      (hsurv_summable G).tsum_le_tsum (hdom G) hMajSummable
    have hrough := (h25 B a hB ha).2.1
    have hformula :
        Real.log B / a + 2 + 1 / a =
          2 * (q : ℝ) * Fintype.card V * Real.log (q : ℝ) + 2 * q + 2 := by
      dsimp [B, a]
      rw [Real.log_pow]
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
      field_simp
      ring
    calc
      (∑' k : ℕ, survival q G k) ≤ ∑' k : ℕ, majorant k := hle
      _ ≤ Real.log B / a + 2 + 1 / a := hrough
      _ = 2 * (q : ℝ) * Fintype.card V * Real.log (q : ℝ) + 2 * q + 2 := hformula
  have hlife_eq (G : MGraph V) :
      lifetime q G = ENNReal.ofReal (∑' k : ℕ, survival q G k) := by
    unfold lifetime
    exact (ENNReal.ofReal_tsum_of_nonneg (fun k => hsurv_nonneg G k)
      (hsurv_summable G)).symm
  have htsum_nonneg (G : MGraph V) : 0 ≤ ∑' k : ℕ, survival q G k :=
    tsum_nonneg (fun k => hsurv_nonneg G k)
  have hlife_real_eq (G : MGraph V) :
      lifetimeReal q G = ∑' k : ℕ, survival q G k := by
    unfold lifetimeReal
    rw [hlife_eq G, ENNReal.toReal_ofReal (htsum_nonneg G)]
  have hconstant_pos : 0 < lifetimeConstant q := by
    have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    unfold lifetimeConstant
    positivity
  refine ⟨hconstant_pos, ?_, ?_, ?_, ?_⟩
  · intro G
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hlife_eq G]
      exact ENNReal.ofReal_ne_top
    · rw [hlife_real_eq G]
      exact htsum_nonneg G
    · rw [hlife_real_eq G]
      exact hsum_bound G
    · rw [hlife_real_eq G]
      have hcoeff :
          2 * (q : ℝ) + 2 ≤ (2 * (q : ℝ) + 1) * (Fintype.card V : ℝ) := by
        have hNge : (2 : ℝ) ≤ Fintype.card V := hN
        have hfactor : 0 ≤ 2 * (q : ℝ) + 1 := by positivity
        nlinarith
      have hbound := hsum_bound G
      unfold lifetimeConstant
      nlinarith
  · unfold infiniteHittingProbability
    let p : ℕ → ℝ := fun k => processSurvival (V := V) q k
    change sInf (Set.range p) = 0
    apply le_antisymm
    ·
      have hpBdd : BddBelow (Set.range p) := by
        refine ⟨0, ?_⟩
        rintro x ⟨k, rfl⟩
        exact hsurv_nonneg (0 : MGraph V) k
      have hInfBound : ∀ k : ℕ, sInf (Set.range p) ≤ p k := by
        intro k
        exact csInf_le hpBdd (Set.mem_range_self k)
      have htend : Tendsto p atTop (𝓝 0) := by
        exact (hsurv_summable (0 : MGraph V)).tendsto_atTop_zero
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend hInfBound
    · apply le_csInf (Set.range_nonempty p)
      rintro x ⟨k, rfl⟩
      exact hsurv_nonneg (0 : MGraph V) k
  · exact hsurv_summable (0 : MGraph V)
  · simpa [processSurvival] using (hlife_real_eq (0 : MGraph V)).symm

end ThLean.W.S328

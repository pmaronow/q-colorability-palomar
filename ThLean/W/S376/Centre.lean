import ThLean.BP.S3.Centre

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S376
open ThresholdFoundations

private lemma exists_nat_mul_exp_neg_threshold {a d ε : ℝ}
    (hd : 0 < d) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a * Real.exp (-((n : ℝ) * d)) < ε := by
  have hlinear : Tendsto (fun n : ℕ => (n : ℝ) * d) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hd
  have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * d))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
  have hlim : Tendsto (fun n : ℕ => a * Real.exp (-((n : ℝ) * d))) atTop (𝓝 0) := by
    simpa using hexp.const_mul a
  have hevent : ∀ᶠ n : ℕ in atTop, a * Real.exp (-((n : ℝ) * d)) < ε :=
    (tendsto_order.1 hlim).2 ε hε
  exact eventually_atTop.1 hevent

private theorem cappedTail_antitone_local {V : Type*} [Fintype V]
    (q M m k : ℕ) (hmk : m ≤ k) :
    cappedTail (V := V) q M k ≤ cappedTail (V := V) q M m := by
  unfold cappedTail uniformProb uniformMean
  apply div_le_div_of_nonneg_right
  · apply Finset.sum_le_sum
    intro x hx
    by_cases hk : k ≤ cappedLast q x
    · have hm : m ≤ cappedLast q x := hmk.trans hk
      simp [indicator, hk, hm]
    · by_cases hm : m ≤ cappedLast q x <;> simp [indicator, hk, hm]
  · exact Nat.cast_nonneg _

theorem S3_53Statement_of_deps
    (h05 : ThLean.BP.S3.S3_05Statement.{0})
    (h06 : ThLean.BP.S3.S3_06bStatement.{0})
    (h07 : ThLean.BP.S3.S3_07bStatement.{0})
    (h52 : ThLean.BP.S3.S3_52Statement) :
    ThLean.BP.S3.S3_53Statement := by
  intro q Λ η β hq hΛ hη hηle hβ
  have hq2 : 2 ≤ q := by omega
  have hγ1 : 1 ≤ gamma q := (h52 q hq2).2.2.1
  have hlog : 0 < Real.log ((q : ℝ) / ((q : ℝ) - 1)) := (h52 q hq2).1
  have hΛγ : gamma q < Λ := by linarith
  have hβpos : 0 < β := by linarith

  let a : ℝ := Real.log ((q : ℝ) / ((q : ℝ) - 1))
  let Cβ : ℝ := ((q : ℝ) / ((q : ℝ) - 1)) * Real.exp (2 * β)
  let CΛ : ℝ := ((q : ℝ) / ((q : ℝ) - 1)) * Real.exp (2 * Λ)
  let dβ : ℝ := (β - gamma q) * a
  let dΛ : ℝ := (Λ - gamma q) * a
  have ha : 0 < a := hlog
  have hdβ : 0 < dβ := by dsimp [dβ]; exact mul_pos (sub_pos.mpr hβ) ha
  have hdΛ : 0 < dΛ := by dsimp [dΛ]; exact mul_pos (sub_pos.mpr hΛγ) ha

  obtain ⟨Nβ, hNβ⟩ := exists_nat_mul_exp_neg_threshold hdβ hη
  obtain ⟨NΛ, hNΛ⟩ := exists_nat_mul_exp_neg_threshold hdΛ hη
  refine ⟨max Nβ NΛ, ?_⟩
  intro n hn hnq
  have hNβn : Nβ ≤ n := le_trans (le_max_left Nβ NΛ) hn
  have hNΛn : NΛ ≤ n := le_trans (le_max_right Nβ NΛ) hn

  have hcard : 2 ≤ Fintype.card (Fin n) := by
    simp
    omega
  let M : ℕ := cap Λ n
  let L : ℕ := lowerLocation q Λ η n
  let U : ℕ := upperLocation q Λ η n
  have h05' := h05 (Fin n) q M hq2 hcard
  have h06' := h06 (Fin n) q M η hcard hη hηle
  have h07' := h07 (Fin n) q M η hq2 hcard hη hηle
  have hUle : U ≤ M := by
    simpa [U, M, upperLocation] using h06'.2.1
  have hEtaTail : η ≤ cappedTail (V := Fin n) q M U := by
    simpa [U, M, upperLocation] using h06'.2.2.2.1
  have hLU : L ≤ U := by
    simpa [L, U, lowerLocation, upperLocation] using h07'.1
  have hTailId : ∀ m : ℕ, m ≤ M →
      cappedTail (V := Fin n) q M m = processSurvival (V := Fin n) q m :=
    h05'.2.2.1

  have hfirst := h52 q hq2
  have hboundβ : processSurvival (V := Fin n) q (Nat.floor (β * (n : ℝ))) ≤
      Cβ * Real.exp (-((n : ℝ) * dβ)) := by
    have h := hfirst.2.2.2.1 β n hβ hnq
    have harg : -(n : ℝ) * (β - gamma q) * a = -((n : ℝ) * dβ) := by
      dsimp [dβ]
      ring
    rw [harg] at h
    simpa [Cβ, a] using h
  have hboundΛ : processSurvival (V := Fin n) q M ≤
      CΛ * Real.exp (-((n : ℝ) * dΛ)) := by
    have h := hfirst.2.2.2.1 Λ n hΛγ hnq
    have harg : -(n : ℝ) * (Λ - gamma q) * a = -((n : ℝ) * dΛ) := by
      dsimp [dΛ]
      ring
    rw [harg] at h
    simpa [CΛ, a, M, cap] using h
  have hsurvβ : processSurvival (V := Fin n) q (Nat.floor (β * (n : ℝ))) < η :=
    hboundβ.trans_lt (hNβ n hNβn)
  have hsurvΛ : processSurvival (V := Fin n) q M < η :=
    hboundΛ.trans_lt (hNΛ n hNΛn)

  have hUltM : U < M := by
    by_contra hnot
    have hEq : U = M := by omega
    have hηM : η ≤ processSurvival (V := Fin n) q M := by
      rw [← hTailId M (le_rfl : M ≤ M)]
      simpa [hEq] using hEtaTail
    linarith

  have hbetaFloorCast : ((Nat.floor (β * (n : ℝ)) : ℕ) : ℝ) ≤ β * (n : ℝ) :=
    Nat.floor_le (mul_nonneg (le_of_lt hβpos) (Nat.cast_nonneg n))

  have hUfloor : U ≤ Nat.floor (β * (n : ℝ)) := by
    by_cases hfloorM : M ≤ Nat.floor (β * (n : ℝ))
    · exact le_trans hUle hfloorM
    · have hfloorLtM : Nat.floor (β * (n : ℝ)) < M := Nat.lt_of_not_ge hfloorM
      by_contra hnot
      have hfloorLtU : Nat.floor (β * (n : ℝ)) < U := Nat.lt_of_not_ge hnot
      have htailMono := cappedTail_antitone_local (V := Fin n) q M
        (Nat.floor (β * (n : ℝ))) U hfloorLtU.le
      have hηβ : η ≤ processSurvival (V := Fin n) q (Nat.floor (β * (n : ℝ))) := by
        rw [← hTailId (Nat.floor (β * (n : ℝ))) (Nat.le_of_lt hfloorLtM)]
        exact hEtaTail.trans htailMono
      exact (not_lt_of_ge hηβ) (hboundβ.trans_lt (hNβ n hNβn))

  refine ⟨hLU, hUfloor, hbetaFloorCast, ?_⟩
  exact hUltM

end ThLean.W.S376

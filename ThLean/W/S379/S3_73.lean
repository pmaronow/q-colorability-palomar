import ThLean.BP.S3.Centre

noncomputable section
open scoped BigOperators

namespace ThLean.W.S379

open ThLean.BP.S3

private theorem ratio_pow_bound (N k : ℕ) (hN : 2 ≤ N) (hk : k ≤ N) :
    ((N : ℝ) / ((N : ℝ) - 1))^k ≤ Real.exp 2 := by
  let d : ℝ := (N : ℝ) - 1
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hratio : (N : ℝ) / d = 1 + 1 / d := by
    have hN_eq : (N : ℝ) = d + 1 := by dsimp [d]; ring
    rw [hN_eq]
    field_simp [ne_of_gt hd]
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hbase : 1 + 1 / d ≤ Real.exp (1 / d) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / d)
  have hexp : ((N : ℝ) / d)^k ≤ Real.exp ((k : ℝ) * (1 / d)) := by
    calc
      ((N : ℝ) / d)^k = (1 + 1 / d)^k := by rw [hratio]
      _ ≤ Real.exp (1 / d)^k := by gcongr
      _ = Real.exp ((k : ℝ) * (1 / d)) := (Real.exp_nat_mul (1 / d) k).symm
  have hkdiv : (k : ℝ) / d ≤ 2 := by
    rw [div_le_iff₀ hd]
    dsimp [d]
    nlinarith
  have hkdiv' : (k : ℝ) * (1 / d) ≤ 2 := by
    simpa [div_eq_mul_inv] using hkdiv
  have hpow : ((N : ℝ) / d)^k ≤ Real.exp 2 :=
    le_trans hexp (Real.exp_le_exp.mpr hkdiv')
  simpa [d] using hpow

private theorem obstruction_term_bound
    (c : ℝ) (N m k : ℕ)
    (hc0 : 0 < c) (hN : 2 ≤ N)
    (hm : (m : ℝ) ≤ c * N) (hk : k ≤ N) :
    2 * ((k + 2 : ℕ) : ℝ)^2 * (N : ℝ)^k *
        ((m : ℝ) / (N.choose 2 : ℝ))^(k + 1) ≤
      (2 * Real.exp 2 / ((N : ℝ) - 1)) *
        (((k + 2 : ℕ) : ℝ)^2 * (2 * c)^(k + 1)) := by
  let d : ℝ := (N : ℝ) - 1
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hchoose : (N.choose 2 : ℝ) = (N : ℝ) * d / 2 := by
    simpa [d] using (Nat.cast_choose_two ℝ N)
  have hchoose_pos : 0 < (N.choose 2 : ℝ) := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ N))
  have hmR : (m : ℝ) ≤ c * (N : ℝ) := hm
  have hratio_m : (m : ℝ) / (N.choose 2 : ℝ) ≤ (2 * c) / d := by
    rw [div_le_div_iff₀ hchoose_pos hd]
    calc
      (m : ℝ) * d ≤ (c * (N : ℝ)) * d :=
        mul_le_mul_of_nonneg_right hmR (le_of_lt hd)
      _ = (2 * c) * ((N : ℝ) * d / 2) := by ring
      _ = (2 * c) * (N.choose 2 : ℝ) := by rw [hchoose]
  have hratio_pow : ((N : ℝ) / d)^k ≤ Real.exp 2 := by
    simpa [d] using ratio_pow_bound N k hN hk
  have hpow_m : ((m : ℝ) / (N.choose 2 : ℝ))^(k + 1) ≤ ((2 * c) / d)^(k + 1) := by
    gcongr
  have hident : (N : ℝ)^k * ((2 * c) / d)^(k + 1) =
      (2 * c)^(k + 1) * ((1 / d) * ((N : ℝ) / d)^k) := by
    calc
      (N : ℝ)^k * ((2 * c) / d)^(k + 1) =
          ((N : ℝ)^k * ((2 * c) / d)^k) * ((2 * c) / d) := by rw [pow_succ]; ring
      _ = ((N : ℝ) * ((2 * c) / d))^k * ((2 * c) / d) := by rw [← mul_pow]
      _ = ((2 * c) * ((N : ℝ) / d))^k * ((2 * c) / d) := by
          congr 2
          field_simp
      _ = ((2 * c)^k * ((N : ℝ) / d)^k) * ((2 * c) / d) := by rw [mul_pow]
      _ = (2 * c)^(k + 1) * ((1 / d) * ((N : ℝ) / d)^k) := by
          rw [pow_succ]
          field_simp
  calc
    2 * ((k + 2 : ℕ) : ℝ)^2 * (N : ℝ)^k *
        ((m : ℝ) / (N.choose 2 : ℝ))^(k + 1) ≤
        2 * ((k + 2 : ℕ) : ℝ)^2 * (N : ℝ)^k * ((2 * c) / d)^(k + 1) := by
          gcongr
    _ = 2 * ((k + 2 : ℕ) : ℝ)^2 *
        ((N : ℝ)^k * ((2 * c) / d)^(k + 1)) := by ring
    _ = 2 * ((k + 2 : ℕ) : ℝ)^2 *
        ((2 * c)^(k + 1) * ((1 / d) * ((N : ℝ) / d)^k)) := by rw [hident]
    _ ≤ 2 * ((k + 2 : ℕ) : ℝ)^2 *
        ((2 * c)^(k + 1) * ((1 / d) * Real.exp 2)) := by
          gcongr
    _ = (2 * Real.exp 2 / d) *
        (((k + 2 : ℕ) : ℝ)^2 * (2 * c)^(k + 1)) := by ring

theorem S3_73Statement_of_deps (h72 : S3_72Statement) : S3_73Statement := by
  intro c N m hc0 hc1 hN hm
  let d : ℝ := (N : ℝ) - 1
  have hd : 0 < d := by
    dsimp [d]
    have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hpow : ∀ k : ℕ, k ≤ N → ((N : ℝ) / ((N : ℝ) - 1))^k ≤ Real.exp 2 := by
    intro k hk
    exact ratio_pow_bound N k hN hk
  have hs : Summable (fun j : ℕ => ((j + 4 : ℕ) : ℝ)^2 * (2 * c)^(j + 3)) :=
    (h72.1 (2*c) (by positivity) (by linarith)).1
  have hseries_nonneg : 0 ≤ obstructionSeries (2*c) := by
    unfold obstructionSeries
    exact tsum_nonneg (fun j => by positivity)
  have hfinite :
      (∑ k ∈ Finset.Icc 2 N,
        2*((k+2 : ℕ) : ℝ)^2*(N : ℝ)^k*((m : ℝ)/(N.choose 2 : ℝ))^(k+1)) ≤
      (2*Real.exp 2/d) * obstructionSeries (2*c) := by
    have hpoint : ∀ k ∈ Finset.Icc 2 N,
        2*((k+2 : ℕ) : ℝ)^2*(N : ℝ)^k*((m : ℝ)/(N.choose 2 : ℝ))^(k+1) ≤
          (2*Real.exp 2/d) *
            (((k+2 : ℕ) : ℝ)^2 * (2*c)^(k+1)) := by
      intro k hk
      exact obstruction_term_bound c N m k hc0 hN hm (Finset.mem_Icc.mp hk).2
    have hshift :
        (∑ k ∈ Finset.Icc 2 N,
          (((k+2 : ℕ) : ℝ)^2 * (2*c)^(k+1))) =
        ∑ j ∈ Finset.Icc 0 (N-2), (((j+4 : ℕ) : ℝ)^2 * (2*c)^(j+3)) := by
      apply Finset.sum_bij (fun k hk => k-2)
      · intro k hk
        simp only [Finset.mem_Icc] at hk ⊢
        omega
      · intro k₁ hk₁ k₂ hk₂ heq
        simp only [Finset.mem_Icc] at hk₁ hk₂
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        refine ⟨j+2, ?_, ?_⟩
        · simp only [Finset.mem_Icc]
          omega
        · omega
      · intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        rw [show k + 2 = (k - 2) + 4 by omega]
        rw [show k + 1 = (k - 2) + 3 by omega]
    calc
      (∑ k ∈ Finset.Icc 2 N,
          2*((k+2 : ℕ) : ℝ)^2*(N : ℝ)^k*((m : ℝ)/(N.choose 2 : ℝ))^(k+1)) ≤
        ∑ k ∈ Finset.Icc 2 N,
          (2*Real.exp 2/d) * (((k+2 : ℕ) : ℝ)^2 * (2*c)^(k+1)) :=
            Finset.sum_le_sum hpoint
      _ = (2*Real.exp 2/d) *
          (∑ j ∈ Finset.Icc 0 (N-2), (((j+4 : ℕ) : ℝ)^2 * (2*c)^(j+3))) := by
            rw [← Finset.mul_sum, hshift]
      _ ≤ (2*Real.exp 2/d) * obstructionSeries (2*c) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa [obstructionSeries] using
            hs.sum_le_tsum (Finset.Icc 0 (N-2)) (fun j hj => by positivity)
  have hfactor : (2*Real.exp 2/d) ≤ 4*Real.exp 2/(N : ℝ) := by
    rw [div_le_div_iff₀ hd (by positivity : (0 : ℝ) < (N : ℝ))]
    dsimp [d]
    nlinarith [Real.exp_pos (2 : ℝ), (show (2:ℝ) ≤ N by exact_mod_cast hN)]
  have hseries_pos : 0 < obstructionSeries (2*c) := by
    unfold obstructionSeries
    exact hs.tsum_pos (fun j => by positivity) 0 (by norm_num; positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    simpa [d] using hpow k hk
  · simpa [d] using hfinite
  · unfold obstructionConstant
    calc
      (2*Real.exp 2/((N : ℝ)-1)) * obstructionSeries (2*c) ≤
          (4*Real.exp 2/(N : ℝ)) * obstructionSeries (2*c) :=
        mul_le_mul_of_nonneg_right hfactor hseries_nonneg
      _ = 4*Real.exp 2*obstructionSeries (2*c)/(N : ℝ) := by ring
  · unfold obstructionConstant
    positivity

example (h72 : S3_72Statement) : S3_73Statement := S3_73Statement_of_deps h72

end ThLean.W.S379

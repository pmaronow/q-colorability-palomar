module

public import ThLean.BP.S3.Centre

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ThLean.W.S380
open ThresholdFoundations

theorem S3_75Statement_of_deps
    (h05 : ThLean.BP.S3.S3_05Statement.{0})
    (h06b : ThLean.BP.S3.S3_06bStatement.{0})
    (h52 : ThLean.BP.S3.S3_52Statement)
    (h71 : ThLean.BP.S3.S3_71Statement.{0})
    (h73 : ThLean.BP.S3.S3_73Statement) :
    ThLean.BP.S3.S3_75Statement := by
  intro q Λ η c hq hΛ hη0 hη1 hc0 hc1
  let c' : ℝ := (c + 1/2) / 2
  have hc'0 : 0 < c' := by dsimp [c']; linarith
  have hc'1 : c' < 1/2 := by dsimp [c']; linarith
  have hgap : 0 < c' - c := by dsimp [c']; linarith
  have hq2 : 2 ≤ q := by omega
  have hΛ2 : 2 < Λ := ((h52 q hq2).2.2.2.2 Λ hΛ).1
  have hΛc : c + 1 < Λ := by linarith

  obtain ⟨Nslack, hNslack⟩ := exists_nat_gt (1 / (c' - c))
  have hNslack' : 1 < (c' - c) * (Nslack : ℝ) :=
    by simpa [mul_comm] using (div_lt_iff₀ hgap).mp hNslack
  obtain ⟨Nprob, hNprob⟩ :=
    exists_nat_gt (ThLean.BP.S3.obstructionConstant c' / η)
  have hNprob' : ThLean.BP.S3.obstructionConstant c' < η * (Nprob : ℝ) :=
    by simpa [mul_comm] using (div_lt_iff₀ hη0).mp hNprob

  refine ⟨max Nslack Nprob, ?_⟩
  intro n hn0 hnq
  have hnslack : 1 < (c' - c) * (n : ℝ) := by
    have hNle : (Nslack : ℝ) ≤ n := by
      exact_mod_cast (le_trans (le_max_left _ _) hn0)
    exact lt_of_lt_of_le hNslack'
      (mul_le_mul_of_nonneg_left hNle (le_of_lt hgap))
  have hnprob : ThLean.BP.S3.obstructionConstant c' < η * (n : ℝ) := by
    have hNle : (Nprob : ℝ) ≤ n := by
      exact_mod_cast (le_trans (le_max_right _ _) hn0)
    exact lt_of_lt_of_le hNprob'
      (mul_le_mul_of_nonneg_left hNle (le_of_lt hη0))
  have hnpos : 0 < n := by omega
  have hncard : 2 ≤ Fintype.card (Fin n) := by simp; omega
  have hnreal1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  let M : ℕ := cap Λ n
  let L : ℕ := lowerQuantile (V := Fin n) q M η
  have hquant := h06b (Fin n) q M η hncard hη0 hη1
  have hLcdf : η ≤ cappedCDF (V := Fin n) q M L := hquant.2.2.1

  by_contra hgoal
  have hLreal : (L : ℝ) ≤ c * n := by
    dsimp [L, M, lowerLocation] at hgoal ⊢
    exact le_of_not_gt hgoal
  have hcapreal : c * (n : ℝ) < (M : ℝ) := by
    have hmul : (c + 1) * (n : ℝ) < Λ * n :=
      mul_lt_mul_of_pos_right hΛc (by exact_mod_cast hnpos)
    have hfloor := Nat.lt_floor_add_one (Λ * (n : ℝ))
    dsimp [M, cap]
    nlinarith
  have hLlt : L < M := by
    exact_mod_cast (lt_of_le_of_lt hLreal hcapreal)
  have hLshift : ((L + 1 : ℕ) : ℝ) ≤ c' * n := by
    have h := hnslack
    push_cast
    nlinarith [hLreal]

  have hquantcdf :
      cappedCDF (V := Fin n) q M L = 1 - processSurvival (V := Fin n) q (L + 1) :=
    (h05 (Fin n) q M (by omega) hncard).2.2.2.1 L hLlt
  have hsum := h71 (Fin n) q hq hncard (L + 1)
  have hsum' : 1 - processSurvival (V := Fin n) q (L + 1) ≤
      ∑ k ∈ Finset.Icc 2 n,
        2*((k+2 : ℕ) : ℝ)^2*(n : ℝ)^k *
          (((L+1 : ℕ) : ℝ) / (n.choose 2 : ℝ))^(k+1) := by
    simpa only [Fintype.card_fin] using hsum
  have hnum := h73 c' n (L + 1) hc'0 hc'1 (by omega) hLshift
  have hsmall : 1 - processSurvival (V := Fin n) q (L + 1) ≤
      ThLean.BP.S3.obstructionConstant c' / (n : ℝ) :=
    hsum'.trans (hnum.2.1.trans hnum.2.2.1)
  have hratio : ThLean.BP.S3.obstructionConstant c' / (n : ℝ) < η := by
    apply (div_lt_iff₀ (by exact_mod_cast hnpos)).2
    exact hnprob
  rw [hquantcdf] at hLcdf
  linarith

end ThLean.W.S380

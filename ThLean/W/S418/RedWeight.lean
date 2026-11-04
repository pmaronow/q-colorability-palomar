module

public import ThLean.BP.S4.Deletion

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S418
open ThresholdFoundations

theorem S4_RED_05Statement_of_deps (hpre : PreLifetimeStatement.{0}) :
    ThLean.BP.S4.S4_RED_05Statement := by
  intro q n hq hn m U hm hmu G hG
  have hn2 : 2 ≤ n := by omega
  have hncard : 2 ≤ Fintype.card (Fin n) := by simpa using hn2
  have hpreV := hpre (Fin n) q hq hncard
  have hpreG := hpreV.1 G hG
  let b : ℕ := U + 1 - m
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hbR : 1 ≤ (b : ℝ) := by exact_mod_cast hb
  have htrunc := hpreG.2.1 b
  have htrunc_lower (hc : Colorable q G) : 1 ≤ truncatedLifetime q b G :=
    hpreG.2.2.2.1 hc b hb
  have hs0 (hc : Colorable q G) : survival q G 0 = 1 := by
    have hl := htrunc_lower hc
    have hu := (hpreG.2.1 1).2.2
    have hl1 := hpreG.2.2.2.1 hc 1 (by norm_num)
    have hdef : truncatedLifetime q 1 G = survival q G 0 := by
      simp [truncatedLifetime]
    rw [hdef] at hl1 hu
    have hu' : survival q G 0 ≤ 1 := by simpa using hu
    linarith
  have hrange : Finset.range b = Finset.Icc 0 (U - m) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_Icc]
    dsimp [b]
    omega
  have hsplit : Finset.Icc 0 (U - m) = insert 0 (Finset.Icc 1 (U - m)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have htrunc_sum : truncatedLifetime q b G =
      survival q G 0 + ∑ k ∈ Finset.Icc 1 (U - m), survival q G k := by
    unfold truncatedLifetime
    rw [hrange, hsplit, Finset.sum_insert]
    · simp only [Finset.mem_Icc]
      omega
  have hfuture :
      (∑ l ∈ Finset.Icc (m + 1) U, survival q G (l - m)) =
        ∑ k ∈ Finset.Icc 1 (U - m), survival q G k := by
    apply Finset.sum_bij (fun l _ => l - m)
    · intro l hl
      simp only [Finset.mem_Icc] at hl ⊢
      omega
    · intro l₁ hl₁ l₂ hl₂ heq
      simp only [Finset.mem_Icc] at hl₁ hl₂
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      refine ⟨k + m, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · simp
    · intro l hl
      rfl
  refine ⟨hb, ?_, ?_, ?_, ?_⟩
  · by_cases hc : Colorable q G
    · have hl := htrunc_lower hc
      simp [deletionWeight, hc]
      linarith
    · simp [deletionWeight, hc]
  · by_cases hc : Colorable q G
    · have hl := htrunc_lower hc
      simp [deletionWeight, hc]
      have hu := htrunc.2.2
      dsimp [b] at hu
      have huR : truncatedLifetime q b G ≤ (b : ℝ) := by exact_mod_cast hu
      linarith
    · simp [deletionWeight, hc]
      nlinarith
  · by_cases hc : Colorable q G
    · have hweight : deletionWeight q b G =
          1 + 2 * ∑ l ∈ Finset.Icc (m + 1) U, survival q G (l - m) := by
        calc
          deletionWeight q b G = 2 * truncatedLifetime q b G - 1 := by
            simp [deletionWeight, hc]
          _ = 1 + 2 * ∑ l ∈ Finset.Icc (m + 1) U, survival q G (l - m) := by
            rw [htrunc_sum, hs0 hc, ← hfuture]
            ring
      rw [hweight]
    · have hkzero : kappa q G = 0 := by
        simp [kappa, uniformProb, uniformMean, indicator, FrozenPair, Frozen, hc]
      simp [deletionWeight, hc, hkzero]
  · intro hc
    have hl := htrunc_lower hc
    constructor
    · simp [deletionWeight, hc]
      linarith
    · simp [deletionWeight, hc]

end ThLean.W.S418

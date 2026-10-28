import ThLean.BP.SA.Basics

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA18

open ThresholdFoundations

private theorem edgeTuple_nonempty (n M : ℕ) (hn : 2 ≤ n) :
    Nonempty (EdgeTuple (Fin n) M) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    simp [a, b] at hv
  refine ⟨fun _ => ⟨s(a, b), ?_⟩⟩
  intro v hv
  rw [Sym2.eq_iff] at hv
  rcases hv with ⟨hav, hbv⟩ | ⟨hav, hbv⟩
  · exact hab (hav.trans hbv.symm)
  · exact hab (hav.trans hbv.symm)

private theorem uniformProb_congr {A : Type*} [Fintype A] (P Q : A → Prop)
    (h : ∀ a, P a ↔ Q a) : uniformProb P = uniformProb Q := by
  unfold uniformProb uniformMean
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  simp [indicator, h a]

private theorem uniformProb_compl {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) : uniformProb (fun a => ¬ P a) = 1 - uniformProb P := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ‹Nonempty A›))
  have hsum : (∑ a : A, indicator (¬ P a)) =
      ∑ a : A, (1 - indicator (P a)) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : P a <;> simp [indicator, h]
  have hsumone : (∑ _a : A, (1 : ℝ)) = (Fintype.card A : ℝ) := by
    simp
  unfold uniformProb uniformMean
  rw [hsum, Finset.sum_sub_distrib, hsumone]
  field_simp

private theorem uniformProb_true {A : Type*} [Fintype A] [Nonempty A] :
    uniformProb (fun _ : A => True) = 1 := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ‹Nonempty A›))
  unfold uniformProb uniformMean indicator
  simp [hcard]

private theorem lowerQuantile_le_of {V : Type*} [Fintype V]
    (q M : ℕ) (η : ℝ) (m : ℕ) (hm : m ≤ M)
    (hcdf : η ≤ cappedCDF (V := V) q M m) :
    lowerQuantile (V := V) q M η ≤ m := by
  have hex : ∃ k : ℕ, k ≤ M ∧ η ≤ cappedCDF (V := V) q M k := ⟨m, hm, hcdf⟩
  unfold lowerQuantile
  simp only [dif_pos hex]
  exact Nat.find_min' hex ⟨hm, hcdf⟩

private theorem lowerQuantile_le_cap {V : Type*} [Fintype V] (q M : ℕ) (η : ℝ) :
    lowerQuantile (V := V) q M η ≤ M := by
  by_cases hex : ∃ k : ℕ, k ≤ M ∧ η ≤ cappedCDF (V := V) q M k
  · unfold lowerQuantile
    simp only [dif_pos hex]
    exact (Nat.find_spec hex).1
  · simp [lowerQuantile, hex]

private theorem lowerQuantile_mono {V : Type*} [Fintype V] (q M : ℕ)
    {η₁ η₂ : ℝ} (hη : η₁ ≤ η₂) :
    lowerQuantile (V := V) q M η₁ ≤ lowerQuantile (V := V) q M η₂ := by
  by_cases h₂ : ∃ m : ℕ, m ≤ M ∧ η₂ ≤ cappedCDF (V := V) q M m
  · have h₁ : ∃ m : ℕ, m ≤ M ∧ η₁ ≤ cappedCDF (V := V) q M m := by
      obtain ⟨m, hm, hcdf⟩ := h₂
      exact ⟨m, hm, hη.trans hcdf⟩
    simp only [lowerQuantile, dif_pos h₁, dif_pos h₂]
    apply Nat.find_min'
    exact ⟨(Nat.find_spec h₂).1, hη.trans (Nat.find_spec h₂).2⟩
  · have hbound := lowerQuantile_le_cap (V := V) q M η₁
    simp only [lowerQuantile, dif_neg h₂]
    exact hbound

private theorem upperQuantile_le {V : Type*} [Fintype V] (q M : ℕ) (η : ℝ) :
    upperQuantile (V := V) q M η ≤ M := by
  unfold upperQuantile
  split <;> omega

private theorem cappedCDF_tail_compl {V : Type*} [Fintype V] (q M m : ℕ)
    [Nonempty (EdgeTuple V M)] :
    cappedCDF (V := V) q M m = 1 - cappedTail (V := V) q M (m + 1) := by
  have heq : cappedTail (V := V) q M (m + 1) =
      uniformProb (fun x : EdgeTuple V M => ¬ cappedLast q x ≤ m) := by
    unfold cappedTail
    exact uniformProb_congr _ _ (by intro x; simp only [Nat.succ_le_iff]; omega)
  unfold cappedCDF
  rw [heq, uniformProb_compl]
  ring

private theorem upperQuantile_tail_lt {V : Type*} [Fintype V]
    (q M : ℕ) (η : ℝ) [Nonempty (EdgeTuple V M)] (hη : η ≤ 1) :
    ∀ m : ℕ, upperQuantile (V := V) q M η < m → m ≤ M →
      cappedTail (V := V) q M m < η := by
  have hzero : cappedTail (V := V) q M 0 = 1 := by
    unfold cappedTail
    rw [uniformProb_congr
      (fun x : EdgeTuple V M => 0 ≤ cappedLast q x) (fun _ => True)
      (by
        intro x
        constructor
        · intro _
          trivial
        · intro _
          exact Nat.zero_le _)]
    exact uniformProb_true
  have hex : ∃ k : ℕ, k ≤ M ∧ η ≤ cappedTail (V := V) q M (M - k) := by
    refine ⟨M, le_rfl, ?_⟩
    rw [show M - M = 0 by omega, hzero]
    exact hη
  intro m hUm hm
  have hfind : upperQuantile (V := V) q M η = M - Nat.find hex := by
    simp [upperQuantile, hex]
  rw [hfind] at hUm
  by_contra hnot
  have htail : η ≤ cappedTail (V := V) q M m := le_of_not_gt hnot
  have hsmall : M - m < Nat.find hex := by omega
  have hsub : M - (M - m) = m := by omega
  have hspec : η ≤ cappedTail (V := V) q M (M - (M - m)) := by
    rw [hsub]
    exact htail
  have hfindle := Nat.find_min' hex (show M - m ≤ M ∧
    η ≤ cappedTail (V := V) q M (M - (M - m)) from ⟨by omega, hspec⟩)
  omega

theorem SA_F03Statement_holds : ThLean.BP.SA.SA_F03Statement := by
  intro q hq Λ hΛ n hn η₁ η₂ hη₁ hηle hη₂
  let M := cap Λ n
  have hn2 : 2 ≤ n := by omega
  letI : Nonempty (EdgeTuple (Fin n) M) := edgeTuple_nonempty n M hn2
  constructor
  · change lowerQuantile (V := Fin n) q M η₁ ≤ lowerQuantile (V := Fin n) q M η₂
    exact lowerQuantile_mono q M hηle
  · change lowerQuantile (V := Fin n) q M η₂ ≤ upperQuantile (V := Fin n) q M η₁
    by_cases hU : upperQuantile (V := Fin n) q M η₁ = M
    · rw [hU]
      exact lowerQuantile_le_cap (V := Fin n) q M η₂
    · have hUM : upperQuantile (V := Fin n) q M η₁ < M := by
        have hbound := upperQuantile_le (V := Fin n) q M η₁
        omega
      have htail := upperQuantile_tail_lt (V := Fin n) q M η₁
        (show η₁ ≤ 1 by linarith [hηle, hη₂])
        (upperQuantile (V := Fin n) q M η₁ + 1) (by omega) (by omega)
      have hcomp := cappedCDF_tail_compl (V := Fin n) q M
        (upperQuantile (V := Fin n) q M η₁)
      have hηcdf : η₂ ≤ cappedCDF (V := Fin n) q M
          (upperQuantile (V := Fin n) q M η₁) := by
        rw [hcomp]
        linarith [hη₂, hηle, htail]
      exact lowerQuantile_le_of (V := Fin n) q M η₂
        (upperQuantile (V := Fin n) q M η₁)
        (upperQuantile_le (V := Fin n) q M η₁) hηcdf

example : ThLean.BP.SA.SA_F03Statement := SA_F03Statement_holds

end ThLean.W.SA18

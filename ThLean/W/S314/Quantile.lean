import ThLean.BP.S3.Process

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S314
open ThresholdFoundations

private theorem uniformProb_mono {A : Type*} [Fintype A] [Nonempty A]
    {P Q : A → Prop} (hPQ : ∀ a, P a → Q a) :
    uniformProb P ≤ uniformProb Q := by
  unfold uniformProb uniformMean
  have hden : (0 : ℝ) < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty A))
  apply (div_le_div_iff_of_pos_right hden).2
  apply Finset.sum_le_sum
  intro a ha
  by_cases hP : P a
  · have hQ := hPQ a hP
    simp [indicator, hP, hQ]
  · simp [indicator, hP]
    split_ifs <;> norm_num

private theorem uniformProb_eq_one_of_forall {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) (hP : ∀ a, P a) : uniformProb P = 1 := by
  unfold uniformProb uniformMean
  have hsum : (∑ a : A, indicator (P a)) = (Fintype.card A : ℝ) := by
    simp [indicator, hP]
  rw [hsum]
  have hden : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)).ne'
  exact div_self hden

private theorem cappedLast_le (V : Type*) [Fintype V] (q M : ℕ)
    (x : EdgeTuple V M) : cappedLast q x ≤ M := by
  unfold cappedLast
  calc
    (∑ k ∈ Finset.range M,
      if Colorable q (tuplePrefix x (k + 1)) then 1 else 0) ≤
        ∑ _k ∈ Finset.range M, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro k hk
          split_ifs <;> omega
    _ = M := by simp

theorem S3_06bStatement_holds : ThLean.BP.S3.S3_06bStatement := by
  classical
  intro V hF q M η hV hη hηhalf
  have hcard : 1 < Fintype.card V := by omega
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hcard
  let e : Pair V := ⟨s(a, b), by
    intro v hv
    have hh : s(a, b) = s(v, v) := hv
    rw [Sym2.eq_iff] at hh
    rcases hh with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hab (ha.trans hb.symm)
    · exact hab (ha.trans hb.symm)
  ⟩
  letI : Nonempty (EdgeTuple V M) := ⟨fun _ => e⟩
  have hcap : ∀ x : EdgeTuple V M, cappedLast q x ≤ M := by
    intro x
    exact cappedLast_le V q M x
  have hCDFM : cappedCDF (V := V) q M M = 1 := by
    unfold cappedCDF
    apply uniformProb_eq_one_of_forall
    intro x
    exact hcap x
  have hTail0 : cappedTail (V := V) q M 0 = 1 := by
    unfold cappedTail
    apply uniformProb_eq_one_of_forall
    intro x
    exact Nat.zero_le _
  have hCDFmono : ∀ a b : ℕ, a ≤ b →
      cappedCDF (V := V) q M a ≤ cappedCDF (V := V) q M b := by
    intro a b hab
    apply uniformProb_mono
    intro x hax
    exact le_trans hax hab
  have hTailAnti : ∀ a b : ℕ, a ≤ b →
      cappedTail (V := V) q M b ≤ cappedTail (V := V) q M a := by
    intro a b hab
    apply uniformProb_mono
    intro x hbx
    exact le_trans hab hbx
  have hLwit : ∃ m : ℕ, m ≤ M ∧ η ≤ cappedCDF (V := V) q M m := by
    refine ⟨M, le_rfl, ?_⟩
    rw [hCDFM]
    linarith
  let hL := hLwit
  have hLdef : lowerQuantile (V := V) q M η = Nat.find hL := by
    simp [lowerQuantile, hL]
  have hLbound : Nat.find hL ≤ M := (Nat.find_spec hL).1
  have hLprob : η ≤ cappedCDF (V := V) q M (Nat.find hL) :=
    (Nat.find_spec hL).2
  have hUwit : ∃ k : ℕ, k ≤ M ∧ η ≤ cappedTail (V := V) q M (M - k) := by
    refine ⟨M, le_rfl, ?_⟩
    rw [Nat.sub_self, hTail0]
    linarith
  let hU := hUwit
  have hUdef : upperQuantile (V := V) q M η = M - Nat.find hU := by
    simp [upperQuantile, hU]
  have hUprob : η ≤ cappedTail (V := V) q M (M - Nat.find hU) :=
    (Nat.find_spec hU).2
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLdef]
    exact hLbound
  · rw [hUdef]
    exact Nat.sub_le _ _
  · rw [hLdef]
    exact hLprob
  · rw [hUdef]
    exact hUprob
  · intro m hm
    rw [hLdef] at hm
    have hnot := Nat.find_min hL hm
    have hprob : ¬ η ≤ cappedCDF (V := V) q M m := by
      intro hp
      apply hnot
      exact ⟨by omega, hp⟩
    exact lt_of_not_ge hprob
  · intro m hUm hm
    rw [hUdef] at hUm
    have hkm : M - m < Nat.find hU := by omega
    have hnot := Nat.find_min hU hkm
    have hprob : ¬ η ≤ cappedTail (V := V) q M m := by
      intro hp
      apply hnot
      refine ⟨by omega, ?_⟩
      have heq : M - (M - m) = m := by omega
      rw [heq]
      exact hp
    exact lt_of_not_ge hprob
  · intro m hprob
    rw [hLdef]
    by_cases hm : m ≤ M
    · exact Nat.find_le (h := hL) ⟨hm, hprob⟩
    · exact le_trans hLbound (Nat.le_of_lt (lt_of_not_ge hm))

end ThLean.W.S314

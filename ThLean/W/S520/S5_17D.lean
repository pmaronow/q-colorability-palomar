import ThLean.BP.S5.Identification

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S520

open ThresholdFoundations

private theorem uniformMeanENN_mono {A : Type*} [Fintype A]
    (f g : A → ℝ≥0∞) (h : ∀ a, f a ≤ g a) :
    uniformMeanENN f ≤ uniformMeanENN g := by
  unfold uniformMeanENN
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right
  · exact Finset.sum_le_sum fun a _ => h a
  · positivity

private theorem uniformMeanENN_const {A : Type*} [Fintype A] [Nonempty A]
    (c : ℝ≥0∞) : uniformMeanENN (fun _ : A => c) = c := by
  unfold uniformMeanENN
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right
    (by exact_mod_cast Fintype.card_ne_zero) (by simp)

private theorem uniformMeanENN_indicator_eq {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) :
    uniformMeanENN (fun a => ENNReal.ofReal (indicator (P a))) =
      ENNReal.ofReal (uniformProb P) := by
  unfold uniformMeanENN uniformProb uniformMean indicator
  have hcardPos : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›)
  have hsum : ENNReal.ofReal (∑ a : A, if P a then (1 : ℝ) else 0) =
      ∑ a : A, ENNReal.ofReal (if P a then (1 : ℝ) else 0) :=
    ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun a => if P a then (1 : ℝ) else 0) (by
        intro a ha
        split_ifs <;> norm_num)
  rw [ENNReal.ofReal_div_of_pos hcardPos, ← hsum]
  simp

theorem S5_17DStatement_of_deps
    (hLifetime : ThresholdFoundations.PreLifetimeStatement.{0}) :
    ThLean.BP.S5.S5_17DStatement := by
  intro V inst q hq hV D hD hDV
  letI : Fintype V := inst
  have hsubset : Nonempty (UniformSubset V D) := by
    obtain ⟨Z, hZsub, hZcard⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset V)) hDV
    exact ⟨⟨Z, hZcard⟩⟩
  letI : Nonempty (UniformSubset V D) := hsubset
  have hCard2 : 2 ≤ Fintype.card V := by omega
  have hLifeFacts := hLifetime V q hq hCard2
  have hPair : Nonempty (Pair V) := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := V) (by omega)
    refine ⟨⟨s(a, b), ?_⟩⟩
    intro v hv
    rw [Sym2.eq_iff] at hv
    rcases hv with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hab (ha.trans hb.symm)
    · exact hab (ha.trans hb.symm)
  letI : Nonempty (Pair V) := hPair
  have hEmptyLoopless : Loopless (0 : MGraph V) := by
    intro v
    rfl
  have hLifetimeBound := ((hLifeFacts.1 (0 : MGraph V) hEmptyLoopless).2.2.2.2 hV).1
  apply le_trans ?_ hLifetimeBound
  unfold identificationAdvance lifetime
  apply ENNReal.tsum_le_tsum
  intro m
  calc
    uniformMeanENN (fun x : EdgeTuple V m =>
        uniformMeanENN (fun Z : UniformSubset V D =>
          if Colorable q (tupleGraph x) ∧
              ¬ Colorable q (identify (tupleGraph x) Z.val) then 1 else 0))
        ≤ uniformMeanENN (fun x : EdgeTuple V m =>
            ENNReal.ofReal (indicator (Colorable q (tupleGraph x)))) := by
      apply uniformMeanENN_mono
      intro x
      by_cases hc : Colorable q (tupleGraph x)
      · calc
          uniformMeanENN (fun Z : UniformSubset V D =>
              if Colorable q (tupleGraph x) ∧
                  ¬ Colorable q (identify (tupleGraph x) Z.val) then 1 else 0)
              ≤ uniformMeanENN (fun _ : UniformSubset V D => (1 : ℝ≥0∞)) := by
            apply uniformMeanENN_mono
            intro Z
            split_ifs <;> norm_num
          _ = 1 := uniformMeanENN_const 1
          _ = ENNReal.ofReal (indicator (Colorable q (tupleGraph x))) := by
            simp [indicator, hc]
      · simp [uniformMeanENN, hc]
    _ = ENNReal.ofReal (uniformProb (fun x : EdgeTuple V m =>
        Colorable q (tupleGraph x))) := by
      exact uniformMeanENN_indicator_eq
        (A := EdgeTuple V m) (P := fun x => Colorable q (tupleGraph x))
    _ = ENNReal.ofReal (survival q (0 : MGraph V) m) := by
      congr 1
      simp [survival]

example (hLifetime : ThresholdFoundations.PreLifetimeStatement.{0}) :
    ThLean.BP.S5.S5_17DStatement :=
  S5_17DStatement_of_deps hLifetime

end ThLean.W.S520

module

public import ThLean.BP.SA.Transfer
public import ThLean.BP.SA.Basics

@[expose] public section

noncomputable section
open ThresholdFoundations
attribute [local instance] Classical.propDecidable
namespace ThLean.W.SA70

private theorem uniformProb_mono_finite {A : Type} [Fintype A]
    (P Q : A → Prop) (hPQ : ∀ a, P a → Q a) :
    uniformProb P ≤ uniformProb Q := by
  unfold uniformProb uniformMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (Fintype.card A))
  apply Finset.sum_le_sum
  intro a ha
  by_cases hp : P a
  · have hq : Q a := hPQ a hp
    simp [indicator, hp, hq]
  · simp [indicator, hp]
    split_ifs <;> norm_num

private theorem uniformProb_partition_finite {A : Type} [Fintype A]
    (P Q : A → Prop) :
    uniformProb P = uniformProb (fun a => P a ∧ Q a) +
      uniformProb (fun a => P a ∧ ¬ Q a) := by
  have hsum : (∑ a : A, indicator (P a)) =
      (∑ a : A, indicator (P a ∧ Q a)) +
        (∑ a : A, indicator (P a ∧ ¬ Q a)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hp : P a <;> by_cases hq : Q a <;>
      simp [indicator, hp, hq]
  unfold uniformProb uniformMean
  rw [← add_div]
  exact congrArg (fun z : ℝ => z / (Fintype.card A : ℝ)) hsum

private theorem uniformProb_fintype_eq {A : Type} (f g : Fintype A)
    (P : A → Prop) : @uniformProb A f P = @uniformProb A g P := by
  classical
  have hu : @Finset.univ A f = @Finset.univ A g := by
    ext a
    simp
  have hsum : (@Finset.univ A f).sum (fun a => indicator (P a)) =
      (@Finset.univ A g).sum (fun a => indicator (P a)) :=
    congrArg (fun t : Finset A => t.sum (fun a => indicator (P a))) hu
  have hcard : @Fintype.card A f = @Fintype.card A g := by
    change (@Finset.univ A f).card = (@Finset.univ A g).card
    exact congrArg Finset.card hu
  unfold uniformProb uniformMean
  rw [hsum, hcard]

theorem SA_X52aStatement_of_deps
    (h50c : ThLean.BP.SA.SA_X50cStatement)
    (hF00 : ThLean.BP.SA.SA_F00Statement) :
    ThLean.BP.SA.SA_X52aStatement := by
  intro q n m Λ hq hn hm hcollision
  let D : EdgeTuple (Fin n) m → Prop := fun x => DistinctPrefix x
  let C : EdgeTuple (Fin n) m → Prop := fun x => Colorable q (tupleGraph x)
  let d : ℝ := ThLean.BP.SA.distinctProbability n m
  let s : ℝ := simpleProbability (V := Fin n) q m
  let p : ℝ := processSurvival (V := Fin n) q m

  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  have h01 : v0 ≠ v1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [v0, v1] at hv
  have hpairs : Nonempty (Pair (Fin n)) := by
    refine ⟨⟨s(v0, v1), ?_⟩⟩
    intro v hv
    have heq := (Sym2.eq_iff).mp hv
    rcases heq with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact h01 (h0.trans h1.symm)
    · exact h01 (h0.trans h1.symm)
  have hTupleNonempty : Nonempty (EdgeTuple (Fin n) m) :=
    ⟨fun _ => Classical.choice hpairs⟩

  have hD : uniformProb D = d := by
    simp [D, d, ThLean.BP.SA.distinctProbability]
  have hJoint : uniformProb (fun x => D x ∧ C x) = d * s := by
    dsimp [D, C, d, s]
    exact h50c q n m hq hn hm
  have hProcess : p = uniformProb C := by
    dsimp [p, C, processSurvival, survival]
    simp only [zero_add]
    exact uniformProb_fintype_eq _ _ C

  have hComplement : uniformProb (fun x : EdgeTuple (Fin n) m => ¬ C x) =
      1 - uniformProb C := by
    exact (@hF00.1 (EdgeTuple (Fin n) m) inferInstance hTupleNonempty C).2.2
  have hProcessComplement : uniformProb (fun x : EdgeTuple (Fin n) m => ¬ C x) =
      1 - p := by
    rw [hComplement, hProcess]

  have hPartition := uniformProb_partition_finite D C
  have hPartition' : d = d * s +
      uniformProb (fun x : EdgeTuple (Fin n) m => D x ∧ ¬ C x) := by
    calc
      d = uniformProb D := hD.symm
      _ = uniformProb (fun x => D x ∧ C x) +
          uniformProb (fun x => D x ∧ ¬ C x) := hPartition
      _ = d * s + uniformProb (fun x => D x ∧ ¬ C x) := by rw [hJoint]
  have hNotJoint : uniformProb (fun x : EdgeTuple (Fin n) m => D x ∧ ¬ C x) =
      d * (1 - s) := by
    calc
      uniformProb (fun x => D x ∧ ¬ C x) = d - d * s := by linarith [hPartition']
      _ = d * (1 - s) := by ring

  have hJointLE : uniformProb (fun x : EdgeTuple (Fin n) m => D x ∧ C x) ≤ p := by
    calc
      uniformProb (fun x => D x ∧ C x) ≤ uniformProb C :=
        uniformProb_mono_finite (fun x => D x ∧ C x) C (fun _ hx => hx.2)
      _ = p := hProcess.symm
  have hNotJointLE : uniformProb (fun x : EdgeTuple (Fin n) m => D x ∧ ¬ C x) ≤
      1 - p := by
    calc
      uniformProb (fun x => D x ∧ ¬ C x) ≤ uniformProb (fun x => ¬ C x) :=
        uniformProb_mono_finite _ _ (fun _ hx => hx.2)
      _ = 1 - p := hProcessComplement

  have hSimpleBounds := (hF00.2.2.1) q n m hq hn hm
  have hs0 : 0 ≤ s := hSimpleBounds.1
  have hs1 : s ≤ 1 := hSimpleBounds.2

  have hexp : Real.exp (2 * Λ ^ 2 + 1) * Real.exp (-2 * Λ ^ 2 - 1) = 1 := by
    rw [← Real.exp_add]
    have hsum : (2 * Λ ^ 2 + 1) + (-2 * Λ ^ 2 - 1) = 0 := by ring
    rw [hsum, Real.exp_zero]

  have hbaseC : Real.exp (-2 * Λ ^ 2 - 1) * s ≤ p := by
    calc
      Real.exp (-2 * Λ ^ 2 - 1) * s ≤ d * s :=
        mul_le_mul_of_nonneg_right hcollision hs0
      _ = uniformProb (fun x : EdgeTuple (Fin n) m => D x ∧ C x) := hJoint.symm
      _ ≤ p := hJointLE
  have hscaledC := mul_le_mul_of_nonneg_left hbaseC
    (Real.exp_nonneg (2 * Λ ^ 2 + 1))
  have hCfinal : s ≤ Real.exp (2 * Λ ^ 2 + 1) * p := by
    calc
      s = 1 * s := by ring
      _ = (Real.exp (2 * Λ ^ 2 + 1) * Real.exp (-2 * Λ ^ 2 - 1)) * s := by
        rw [hexp]
      _ = Real.exp (2 * Λ ^ 2 + 1) *
          (Real.exp (-2 * Λ ^ 2 - 1) * s) := by ring
      _ ≤ Real.exp (2 * Λ ^ 2 + 1) * p := hscaledC

  have hbaseNotC : Real.exp (-2 * Λ ^ 2 - 1) * (1 - s) ≤ 1 - p := by
    calc
      Real.exp (-2 * Λ ^ 2 - 1) * (1 - s) ≤ d * (1 - s) :=
        mul_le_mul_of_nonneg_right hcollision (sub_nonneg.mpr hs1)
      _ = uniformProb (fun x : EdgeTuple (Fin n) m => D x ∧ ¬ C x) := hNotJoint.symm
      _ ≤ 1 - p := hNotJointLE
  have hscaledNotC := mul_le_mul_of_nonneg_left hbaseNotC
    (Real.exp_nonneg (2 * Λ ^ 2 + 1))
  have hNotCfinal : 1 - s ≤ Real.exp (2 * Λ ^ 2 + 1) * (1 - p) := by
    calc
      1 - s = 1 * (1 - s) := by ring
      _ = (Real.exp (2 * Λ ^ 2 + 1) * Real.exp (-2 * Λ ^ 2 - 1)) * (1 - s) := by
        rw [hexp]
      _ = Real.exp (2 * Λ ^ 2 + 1) *
          (Real.exp (-2 * Λ ^ 2 - 1) * (1 - s)) := by ring
      _ ≤ Real.exp (2 * Λ ^ 2 + 1) * (1 - p) := hscaledNotC

  exact ⟨by simpa [s, p] using hNotCfinal, by simpa [s, p] using hCfinal⟩

end ThLean.W.SA70

module

public import ThLean.Defs.Bridge

@[expose] public section

noncomputable section
open scoped BigOperators

namespace ThLean.W.BR05

open ThresholdFoundations

private def pairEquiv (n : ℕ) : ThresholdChallenge.Pair n ≃ Pair (Fin n) where
  toFun p := ⟨p.1, by simpa [ThresholdChallenge.Pair, ThresholdChallenge.completeEdges,
    ThresholdFoundations.Pair, ThresholdFoundations.completeEdges] using p.2⟩
  invFun p := ⟨p.1, by simpa [ThresholdChallenge.Pair, ThresholdChallenge.completeEdges,
    ThresholdFoundations.Pair, ThresholdFoundations.completeEdges] using p.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl

private def tupleEquiv (n m : ℕ) : ThresholdChallenge.EdgePrefix n m ≃ EdgeTuple (Fin n) m :=
  Equiv.arrowCongr (Equiv.refl (Fin m)) (pairEquiv n)

private theorem internalTupleColorable_iff (q n m : ℕ)
    (x : ThresholdChallenge.EdgePrefix n m) :
    ThresholdChallenge.MultigraphColorable q (ThresholdChallenge.prefixMultigraph x) ↔
      Colorable q (tupleGraph (tupleEquiv n m x)) := by
  classical
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro u v huv
    have hex : ∃ i : Fin m, (tupleEquiv n m x i).val = s(u, v) := by
      rw [tupleGraph] at huv
      have hne : (Finset.univ.filter fun i : Fin m =>
          (tupleEquiv n m x i).val = s(u, v)).Nonempty := by
        exact Finset.card_pos.mp huv
      rcases hne with ⟨i, hi⟩
      exact ⟨i, (Finset.mem_filter.mp hi).2⟩
    rcases hex with ⟨i, hi⟩
    have hmem : x i ∈ ThresholdChallenge.prefixMultigraph x := by
      change x i ∈ (List.ofFn x : Multiset (ThresholdChallenge.Pair n))
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    have hi' : (x i).val = s(u, v) := by simpa [tupleEquiv, pairEquiv] using hi
    exact hσ (x i) hmem u v hi'
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro e he u v hev
    change e ∈ (List.ofFn x : Multiset (ThresholdChallenge.Pair n)) at he
    simp only [Multiset.mem_coe, List.mem_ofFn] at he
    rcases he with ⟨i, hxi⟩
    subst e
    apply hσ u v
    rw [tupleGraph]
    apply Finset.card_pos.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change (pairEquiv n (x i)).val = s(u, v)
    exact hev

private theorem survival_transport (q n m : ℕ) :
    ThresholdChallenge.processSurvival q n m = processSurvival (V := Fin n) q m := by
  classical
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  letI : DecidablePred (fun e : Sym2 (Fin n) => ∀ v : Fin n, e ≠ s(v, v)) := by
    intro e
    exact @Fintype.decidableForallFintype (Fin n) (fun v => e ≠ s(v, v))
      (fun v => inferInstance) (Fin.fintype n)
  unfold ThresholdChallenge.processSurvival processSurvival
  let e := tupleEquiv n m
  have hcard : Fintype.card (ThresholdChallenge.EdgePrefix n m) =
      Fintype.card (EdgeTuple (Fin n) m) := Fintype.card_congr e
  have hnum : ((Finset.univ.filter fun x : ThresholdChallenge.EdgePrefix n m =>
      ThresholdChallenge.MultigraphColorable q (ThresholdChallenge.prefixMultigraph x)).card : ℝ) =
      ∑ y : EdgeTuple (Fin n) m, indicator (Colorable q (tupleGraph y)) := by
    rw [Finset.card_filter]
    push_cast
    apply Fintype.sum_equiv e
    intro x
    simp only [indicator]
    rw [show Colorable q (tupleGraph (e x)) ↔
      ThresholdChallenge.MultigraphColorable q (ThresholdChallenge.prefixMultigraph x) from
        (internalTupleColorable_iff q n m x).symm]
  rw [hnum, hcard]
  simp [survival, uniformProb, uniformMean, tupleGraph, zero_add]

private theorem rounded_bounds (a : ℤ) (w : ℝ) (k : ℕ)
    (h : |((k + 1 : ℕ) : ℝ) - (a : ℝ)| ≤ w) :
    max 1 (Int.ceil ((a : ℝ) - w)) ≤ (k + 1 : ℤ) ∧
      (k + 1 : ℤ) ≤ Int.floor ((a : ℝ) + w) := by
  have habs := abs_le.mp h
  constructor
  · apply max_le
    · omega
    · apply Int.ceil_le.mpr
      have hlo : (a : ℝ) - w ≤ ((k + 1 : ℕ) : ℝ) := by linarith
      simpa using hlo
  · apply Int.le_floor.mpr
    have hhi : ((k + 1 : ℕ) : ℝ) ≤ (a : ℝ) + w := by linarith
    simpa using hhi

private theorem interval_bounds_abs (a : ℤ) (w : ℝ) (k : ℕ)
    {A B : ℤ} (hA : A = max 1 (Int.ceil ((a : ℝ) - w)))
    (hB : B = Int.floor ((a : ℝ) + w))
    (hlo : A ≤ (k + 1 : ℤ)) (hhi : (k + 1 : ℤ) ≤ B) :
    |((k + 1 : ℕ) : ℝ) - (a : ℝ)| ≤ w := by
  have hceil : Int.ceil ((a : ℝ) - w) ≤ (k + 1 : ℤ) := by
    rw [hA] at hlo
    exact (le_trans (le_max_right _ _) hlo)
  have hfloor : (k + 1 : ℤ) ≤ Int.floor ((a : ℝ) + w) := by
    simpa [hB] using hhi
  have hrealLower : (a : ℝ) - w ≤ ((k + 1 : ℤ) : ℝ) := Int.ceil_le.mp hceil
  have hrealUpper : ((k + 1 : ℤ) : ℝ) ≤ (a : ℝ) + w := Int.le_floor.mp hfloor
  have hcast : ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℤ) : ℝ) := by norm_num
  rw [abs_le]
  constructor <;> rw [hcast] <;> linarith

private theorem window_survival_identity (q n : ℕ) (a : ℤ) (w : ℝ) :
    hittingWindowProbability (V := Fin n) q a w =
      (let A : ℤ := max 1 (Int.ceil ((a : ℝ)-w))
       let B : ℤ := Int.floor ((a : ℝ)+w)
       if A ≤ B then processSurvival (V := Fin n) q (A-1).toNat -
         processSurvival (V := Fin n) q B.toNat else 0) := by
  classical
  let A : ℤ := max 1 (Int.ceil ((a : ℝ) - w))
  let B : ℤ := Int.floor ((a : ℝ) + w)
  by_cases hAB : A ≤ B
  · have hApos : 1 ≤ A := by
      dsimp [A]
      exact le_max_left _ _
    have hBpos : 1 ≤ B := le_trans hApos hAB
    have hA0 : 0 ≤ A := by omega
    have hB0 : 0 ≤ B := by omega
    have hAcast : (A.toNat : ℤ) = A := Int.toNat_of_nonneg hA0
    have hBcast : (B.toNat : ℤ) = B := Int.toNat_of_nonneg hB0
    have hupper : Nat.floor ((a : ℝ) + w) = B.toNat := by
      dsimp [B]
      exact (Int.floor_toNat ((a : ℝ) + w)).symm
    have hset :
        (Finset.range B.toNat).filter
          (fun k => |((k + 1 : ℕ) : ℝ) - (a : ℝ)| ≤ w) =
          Finset.Ico (A.toNat - 1) B.toNat := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hk, habs⟩
        have hround := rounded_bounds a w k habs
        have hroundA : A ≤ (k + 1 : ℤ) := by simpa [A] using hround.1
        have hroundB : (k + 1 : ℤ) ≤ B := by simpa [B] using hround.2
        have hlo : A.toNat ≤ k + 1 := by
          apply Int.toNat_le.mpr
          simpa [hAcast] using hroundA
        have hhi : k + 1 ≤ B.toNat := by
          have hcast : ((k + 1 : ℕ) : ℤ) ≤ (B.toNat : ℤ) := by
            rw [hBcast]
            exact hroundB
          exact_mod_cast hcast
        omega
      · intro hk
        have hloNat : A.toNat ≤ k + 1 := by omega
        have hhiNat : k + 1 ≤ B.toNat := by omega
        have hlo : A ≤ (k + 1 : ℤ) := by
          rw [← hAcast]
          exact_mod_cast hloNat
        have hhi : (k + 1 : ℤ) ≤ B := by
          rw [← hBcast]
          exact_mod_cast hhiNat
        exact ⟨by omega, interval_bounds_abs a w k rfl rfl hlo hhi⟩
    change hittingWindowProbability (V := Fin n) q a w =
      if A ≤ B then processSurvival (V := Fin n) q (A - 1).toNat -
        processSurvival (V := Fin n) q B.toNat else 0
    unfold hittingWindowProbability hittingMass
    rw [hupper]
    rw [← Finset.sum_filter, hset]
    have hle : A.toNat - 1 ≤ B.toNat := by omega
    have hidx : (A - 1).toNat = A.toNat - 1 := by
      have hleft := Int.toNat_of_nonneg (show 0 ≤ A - 1 by omega)
      have hright := Int.toNat_of_nonneg hA0
      omega
    rw [if_pos hAB, hidx]
    have htel := Finset.sum_Ico_sub
      (fun k : ℕ => -processSurvival (V := Fin n) q k) hle
    calc
      (∑ k ∈ Finset.Ico (A.toNat - 1) B.toNat,
          (processSurvival (V := Fin n) q k -
            processSurvival (V := Fin n) q (k + 1))) =
          ∑ k ∈ Finset.Ico (A.toNat - 1) B.toNat,
            ((-processSurvival (V := Fin n) q (k + 1)) -
              (-processSurvival (V := Fin n) q k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = processSurvival (V := Fin n) q (A.toNat - 1) -
          processSurvival (V := Fin n) q B.toNat := by
            simpa [sub_eq_add_neg, add_comm] using htel
  · have hset :
        (Finset.range (Nat.floor ((a : ℝ) + w))).filter
          (fun k => |((k + 1 : ℕ) : ℝ) - (a : ℝ)| ≤ w) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro k hk
      intro habs
      have hround := rounded_bounds a w k habs
      exact hAB (le_trans hround.1 hround.2)
    change hittingWindowProbability (V := Fin n) q a w =
      if A ≤ B then processSurvival (V := Fin n) q (A - 1).toNat -
        processSurvival (V := Fin n) q B.toNat else 0
    unfold hittingWindowProbability hittingMass
    rw [← Finset.sum_filter, hset]
    rw [if_neg hAB]
    simp

theorem WindowProbabilityStatement_holds : ThresholdFoundations.WindowProbabilityStatement := by
  intro q n hq hn a w
  constructor
  · -- Both public and internal definitions count the same edge-prefix samples.
    -- The equivalence transports their finite survival probabilities, hence each mass and sum.
    simp_rw [ThresholdChallenge.hittingWindowProbability,
      ThresholdFoundations.hittingWindowProbability,
      ThresholdChallenge.hittingMass, ThresholdFoundations.hittingMass,
      survival_transport]
  · exact window_survival_identity q n a w

end ThLean.W.BR05

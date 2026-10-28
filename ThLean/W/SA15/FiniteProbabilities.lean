import ThLean.BP.SA.Basics

noncomputable section
open scoped BigOperators

namespace ThLean.W.SA15

open ThresholdFoundations

section UniformProbability

attribute [local instance] Classical.propDecidable

private theorem uniformProb_eq_filter_card {A : Type*} [Fintype A]
    (P : A → Prop) :
    uniformProb P = ((Finset.univ.filter P).card : ℝ) / (Fintype.card A : ℝ) := by
  unfold uniformProb uniformMean
  change (∑ a ∈ (Finset.univ : Finset A), indicator (P a)) / _ = _
  rw [show (∑ a ∈ (Finset.univ : Finset A), indicator (P a)) =
      ((Finset.univ.filter P).card : ℝ) by
        simp only [indicator]
        exact (Finset.sum_boole (R := ℝ) P Finset.univ)]

private theorem uniformProb_bounds {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) : 0 ≤ uniformProb P ∧ uniformProb P ≤ 1 := by
  classical
  rw [uniformProb_eq_filter_card]
  have hden : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hden)
  · apply (div_le_one hden).2
    exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset A) P)

private theorem uniformProb_complement {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) :
    uniformProb (fun a => ¬ P a) = 1 - uniformProb P := by
  classical
  unfold uniformProb uniformMean
  have hsum : (∑ a, indicator (P a)) + (∑ a, indicator (¬ P a)) =
      (Fintype.card A : ℝ) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ a, (indicator (P a) + indicator (¬ P a))) = ∑ a, 1 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : P a <;> simp [indicator, h]
      _ = (Fintype.card A : ℝ) := by simp
  have hden : (Fintype.card A : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast Fintype.card_pos)
  have hnum :
      (∑ a, indicator (¬ P a)) =
        (Fintype.card A : ℝ) - (∑ a, indicator (P a)) := by
    linarith [hsum]
  rw [show (1 : ℝ) = (Fintype.card A : ℝ) / (Fintype.card A : ℝ) by
    field_simp [hden]]
  rw [← sub_div, div_eq_div_iff hden hden]
  exact congrArg (fun x : ℝ => x * (Fintype.card A : ℝ)) hnum

end UniformProbability

private theorem noLoop_iff_not_isDiag {α : Type*} [DecidableEq α]
    (z : Sym2 α) : (∀ v : α, z ≠ s(v, v)) ↔ ¬ z.IsDiag := by
  induction z using Sym2.ind with
  | h a b => simp [eq_comm]

private def pairNoDiagEquiv (n : ℕ) :
    Pair (Fin n) ≃ {z : Sym2 (Fin n) // ¬ z.IsDiag} where
  toFun p := ⟨p.val, (noLoop_iff_not_isDiag p.val).mp p.property⟩
  invFun p := ⟨p.val, (noLoop_iff_not_isDiag p.val).mpr p.property⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl

private theorem pair_card (n : ℕ) : Fintype.card (Pair (Fin n)) = n.choose 2 := by
  calc
    Fintype.card (Pair (Fin n)) =
        Fintype.card {z : Sym2 (Fin n) // ¬ z.IsDiag} :=
      Fintype.card_congr (pairNoDiagEquiv n)
    _ = (Fintype.card (Fin n)).choose 2 := Sym2.card_subtype_not_diag
    _ = n.choose 2 := by simp

private theorem completeEdges_card (n : ℕ) :
    (completeEdges (V := Fin n)).card = n.choose 2 := by
  classical
  let e : {z : Sym2 (Fin n) // z ∈ completeEdges (V := Fin n)} ≃ Pair (Fin n) := {
    toFun := fun z => ⟨z.val, by simpa [completeEdges] using z.property⟩
    invFun := fun z => ⟨z.val, by simpa [completeEdges] using z.property⟩
    left_inv := by intro z; cases z; rfl
    right_inv := by intro z; cases z; rfl
  }
  calc
    (completeEdges (V := Fin n)).card =
        Fintype.card {z : Sym2 (Fin n) // z ∈ completeEdges (V := Fin n)} := by
      symm
      exact Fintype.card_coe _
    _ = Fintype.card (Pair (Fin n)) := Fintype.card_congr e
    _ = n.choose 2 := pair_card n

private theorem pair_nonempty (n : ℕ) (hn : 2 ≤ n) : Nonempty (Pair (Fin n)) := by
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro h
    have : (0 : ℕ) = 1 := by simpa [u, v] using congrArg Fin.val h
    omega
  refine ⟨⟨s(u, v), ?_⟩⟩
  intro w he
  have he' := (Sym2.eq_iff).mp he
  rcases he' with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact huv (hu.trans hv.symm)
  · exact huv (hu.trans hv.symm)

private theorem edgeTuple_nonempty (n m : ℕ) (hn : 2 ≤ n) :
    Nonempty (EdgeTuple (Fin n) m) := by
  letI : Nonempty (Pair (Fin n)) := pair_nonempty n hn
  exact ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair (Fin n)))⟩

private theorem simpleGraphsWithEdges_nonempty (n m : ℕ)
    (hm : m ≤ n.choose 2) : Nonempty (simpleGraphsWithEdges (V := Fin n) m) := by
  classical
  have hcard : m ≤ (completeEdges (V := Fin n)).card := by
    rw [completeEdges_card]
    exact hm
  obtain ⟨E, hsub, hEcard⟩ := Finset.exists_subset_card_eq hcard
  have hE : E ∈ simpleGraphsWithEdges (V := Fin n) m := by
    simp [simpleGraphsWithEdges, hsub, hEcard]
  exact ⟨⟨E, hE⟩⟩

private theorem binomialWeights_sum (n : ℕ) (p : ℝ) :
    (∑ E ∈ (completeEdges (V := Fin n)).powerset,
      p ^ E.card *
        (1 - p) ^ ((Fintype.card (Fin n)).choose 2 - E.card)) = 1 := by
  have hcard : (completeEdges (V := Fin n)).card =
      (Fintype.card (Fin n)).choose 2 := by
    simpa using completeEdges_card n
  rw [← hcard]
  simpa using (Finset.sum_pow_mul_eq_add_pow p (1 - p)
    (completeEdges (V := Fin n)))

private theorem processSurvival_bounds (q n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    0 ≤ processSurvival (V := Fin n) q m ∧
      processSurvival (V := Fin n) q m ≤ 1 := by
  letI : Nonempty (EdgeTuple (Fin n) m) := edgeTuple_nonempty n m hn
  unfold processSurvival survival
  refine @uniformProb_bounds (EdgeTuple (Fin n) m) ?_ ?_
    (fun x : EdgeTuple (Fin n) m =>
      Colorable q ((0 : MGraph (Fin n)) + tupleGraph x))
  exact edgeTuple_nonempty n m hn

private theorem simpleProbability_bounds (q n m : ℕ) (hn : 2 ≤ n)
    (hm : m ≤ n.choose 2) :
    0 ≤ simpleProbability (V := Fin n) q m ∧
      simpleProbability (V := Fin n) q m ≤ 1 := by
  classical
  have hnonempty : Nonempty (simpleGraphsWithEdges (V := Fin n) m) :=
    simpleGraphsWithEdges_nonempty n m hm
  letI : Nonempty (simpleGraphsWithEdges (V := Fin n) m) := hnonempty
  unfold simpleProbability
  obtain ⟨E, hE⟩ := hnonempty
  have hdenNat : 0 < (simpleGraphsWithEdges (V := Fin n) m).card :=
    Finset.card_pos.mpr ⟨E, hE⟩
  have hnumNat :
      ((simpleGraphsWithEdges (V := Fin n) m).filter
        (fun E => Colorable q (simpleGraph E))).card ≤
      (simpleGraphsWithEdges (V := Fin n) m).card :=
    Finset.card_filter_le _ _
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by exact_mod_cast hdenNat)).2
    exact_mod_cast hnumNat

private theorem bernoulliProbability_bounds (q n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ bernoulliProbability (V := Fin n) q p ∧
      bernoulliProbability (V := Fin n) q p ≤ 1 := by
  classical
  unfold bernoulliProbability
  let S := (completeEdges (V := Fin n)).powerset
  have hnonneg : ∀ E ∈ S,
      0 ≤ p ^ E.card *
        (1 - p) ^ ((Fintype.card (Fin n)).choose 2 - E.card) := by
    intro E hE
    apply mul_nonneg
    · exact pow_nonneg hp0 _
    · exact pow_nonneg (by linarith) _
  have hIndicatorNonneg : ∀ E : Finset (Sym2 (Fin n)),
      0 ≤ indicator (Colorable q (simpleGraph E)) := by
    intro E
    by_cases h : Colorable q (simpleGraph E) <;> simp [indicator, h]
  have hIndicatorLe : ∀ E : Finset (Sym2 (Fin n)),
      indicator (Colorable q (simpleGraph E)) ≤ 1 := by
    intro E
    by_cases h : Colorable q (simpleGraph E) <;> simp [indicator, h]
  constructor
  · apply Finset.sum_nonneg
    intro E hE
    exact mul_nonneg (hnonneg E hE) (hIndicatorNonneg E)
  · calc
      (∑ E ∈ S,
          p ^ E.card *
            (1 - p) ^ ((Fintype.card (Fin n)).choose 2 - E.card) *
            indicator (Colorable q (simpleGraph E))) ≤
          ∑ E ∈ S, p ^ E.card *
            (1 - p) ^ ((Fintype.card (Fin n)).choose 2 - E.card) := by
        apply Finset.sum_le_sum
        intro E hE
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hIndicatorLe E) (hnonneg E hE)
      _ = 1 := binomialWeights_sum n p

theorem SA_F00Statement_holds : ThLean.BP.SA.SA_F00Statement := by
  classical
  unfold ThLean.BP.SA.SA_F00Statement
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A instA instNonempty P
    exact ⟨(uniformProb_bounds P).1, (uniformProb_bounds P).2,
      uniformProb_complement P⟩
  · intro q n hq hn m
    exact processSurvival_bounds q n hn m
  · intro q n m hq hn hm
    exact simpleProbability_bounds q n m hn hm
  · intro q n hq hn p hp0 hp1
    exact bernoulliProbability_bounds q n hn p hp0 hp1

example : ThLean.BP.SA.SA_F00Statement := SA_F00Statement_holds

end ThLean.W.SA15

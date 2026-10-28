import ThLean.W.S391.SplitRoot

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S391
open ThresholdFoundations
universe u

set_option maxHeartbeats 1000000 in
theorem S3_38cStatement_of_deps
    (h37 : ThLean.BP.S3.S3_37cStatement.{0, u}) :
    ThLean.BP.S3.S3_38cStatement.{u} := by
  intro V instV hn t h ht
  let n : ℕ := Fintype.card V
  let e : Unit ⊕ V ≃ Option V := sumOptionEquiv V
  have hncard : 2 ≤ n := by simpa [n] using hn
  have hunitcard : Fintype.card Unit = 1 := by simp
  have hsumcard : Fintype.card (Unit ⊕ V) = n + 1 := by
    simp [n, Fintype.card_sum]
    omega
  have hsumge : 3 ≤ Fintype.card (Unit ⊕ V) := by omega
  have hden : ((Fintype.card (Unit ⊕ V)).choose 2 : ℝ) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    rw [hsumcard, Nat.cast_choose_two]
    push_cast
    ring
  have hchooseV : ((Fintype.card V).choose 2 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [show Fintype.card V = n by rfl, Nat.cast_choose_two]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnR1 : 0 < (n : ℝ) + 1 := by positivity
  have hOuterRate :
      t * ((Fintype.card Unit).choose 2 : ℝ) /
        ((Fintype.card (Unit ⊕ V)).choose 2 : ℝ) = 0 := by
    rw [hunitcard]
    simp
  have hBlockRate :
      t * ((Fintype.card V).choose 2 : ℝ) /
        ((Fintype.card (Unit ⊕ V)).choose 2 : ℝ) =
        ((n : ℝ) - 1) * t / ((n : ℝ) + 1) := by
    rw [hchooseV, hden]
    field_simp [ne_of_gt hnR, ne_of_gt hnR1]
  have hListRate :
      t * Fintype.card V /
        ((Fintype.card (Unit ⊕ V)).choose 2 : ℝ) =
        2 * t / ((n : ℝ) + 1) := by
    rw [hden]
    field_simp [ne_of_gt hnR, ne_of_gt hnR1]
    ring
  have hsplit := h37 Unit V hsumge hn t (fun G => h (relabel e G)) ht
  have hcollapse :
      (fun B : MGraph V => independentPoissonListsMeanENN
        (t * Fintype.card V / ((Fintype.card (Unit ⊕ V)).choose 2 : ℝ))
        (fun xs : Unit → List V =>
          h (relabel e (splitUnionGraph (0 : MGraph Unit) B xs)))) =
      (fun B : MGraph V => uniformPoissonListMeanENN
        (t * Fintype.card V / ((Fintype.card (Unit ⊕ V)).choose 2 : ℝ))
        (fun xs => h (addRoot B xs))) := by
    funext B
    let g : List V → ℝ≥0∞ := fun xs => h (addRoot B xs)
    have hcallback :
        (fun xs : Unit → List V =>
          h (relabel e (splitUnionGraph (0 : MGraph Unit) B xs))) =
        (fun xs : Unit → List V => g (xs ())) := by
      funext xs
      dsimp [g]
      have hEta : xs = (fun _ : Unit => xs ()) := by
        funext a
        cases a
        rfl
      rw [hEta, relabel_splitUnionGraph_unit]
    rw [hcallback]
    exact independentPoissonListsMeanENN_unit _ g
  calc
    poissonGraphMeanENN t h = poissonGraphMeanENN t (fun G => h (relabel e G)) :=
      (poissonGraphMeanENN_relabel e t h).symm
    _ = poissonGraphMeanENN
          (t * ((Fintype.card Unit).choose 2 : ℝ) /
            ((Fintype.card (Unit ⊕ V)).choose 2 : ℝ))
          (fun GA : MGraph Unit => poissonGraphMeanENN
            (t * ((Fintype.card V).choose 2 : ℝ) /
              ((Fintype.card (Unit ⊕ V)).choose 2 : ℝ))
            (fun GB : MGraph V => independentPoissonListsMeanENN
              (t * Fintype.card V / ((Fintype.card (Unit ⊕ V)).choose 2 : ℝ))
              (fun xs : Unit → List V =>
                h (relabel e (splitUnionGraph GA GB xs))))) := hsplit
    _ = poissonGraphMeanENN (((Fintype.card V : ℝ) - 1) * t /
          ((Fintype.card V : ℝ) + 1))
          (fun B : MGraph V => uniformPoissonListMeanENN
            (2 * t / ((Fintype.card V : ℝ) + 1))
            (fun xs => h (addRoot B xs))) := by
      rw [hOuterRate, poissonGraphMeanENN_zero_unit]
      rw [hcollapse]
      rw [hBlockRate, hListRate]

end ThLean.W.S391

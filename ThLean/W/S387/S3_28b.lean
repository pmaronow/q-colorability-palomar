module

public import ThLean.BP.S3.Adapters

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S387
open ThresholdFoundations

variable {V : Type*}

theorem tupleGraph_append {m k : ℕ} (x : EdgeTuple V m) (y : EdgeTuple V k) :
    tupleGraph (Fin.append x y) = tupleGraph x + tupleGraph y := by
  funext e
  simp only [tupleGraph, Pi.add_apply, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_add]
  simp [Fin.append]

theorem uniformMeanENN_append {E : Type*} [Fintype E] [Nonempty E]
    {m k : ℕ} (F : (Fin (m + k) → E) → ℝ≥0∞) :
    uniformMeanENN F = uniformMeanENN (fun x : Fin m → E =>
      uniformMeanENN (fun y : Fin k → E => F (Fin.append x y))) := by
  unfold uniformMeanENN
  rw [Fintype.sum_equiv (Fin.appendEquiv m k).symm
    (fun z : Fin (m + k) → E => F z)
    (fun xy : (Fin m → E) × (Fin k → E) => F (Fin.append xy.1 xy.2))
    (by intro z; exact (congrArg F ((Fin.appendEquiv m k).apply_symm_apply z)).symm)]
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_eq_mul_inv]
    rw [← Finset.sum_mul]
    rw [pow_add]
    rw [show ((Fintype.card E : ℝ≥0∞) ^ m *
        (Fintype.card E : ℝ≥0∞) ^ k)⁻¹ =
        ((Fintype.card E : ℝ≥0∞) ^ k)⁻¹ *
        ((Fintype.card E : ℝ≥0∞) ^ m)⁻¹ by
      calc
        _ = ((Fintype.card E : ℝ≥0∞) ^ m)⁻¹ *
            ((Fintype.card E : ℝ≥0∞) ^ k)⁻¹ :=
              ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp))
        _ = _ := mul_comm _ _]
    ac_rfl

theorem ofReal_uniformProb_indicator {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) :
    ENNReal.ofReal (uniformProb P) =
      uniformMeanENN (fun a => if P a then 1 else 0) := by
  unfold uniformProb uniformMean indicator uniformMeanENN
  rw [ENNReal.ofReal_div_of_pos]
  · rw [ENNReal.ofReal_sum_of_nonneg]
    · have hsum :
          (∑ a : A, ENNReal.ofReal (if P a then (1 : ℝ) else 0)) =
            ↑(Finset.univ.filter P).card := by
        calc
          _ = ∑ a : A, if P a then (1 : ℝ≥0∞) else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            split_ifs <;> norm_num
          _ = ↑(Finset.univ.filter P).card := by
            simp
      have hsumENN :
          (∑ a : A, if P a then (1 : ℝ≥0∞) else 0) =
            ↑(Finset.univ.filter P).card := by
        simp
      rw [hsum, hsumENN]
      simp
    · intro a ha
      split_ifs <;> norm_num
  · exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›)

theorem uniformMeanENN_tsum_comm {A : Type*} [Fintype A]
    (f : A → ℕ → ℝ≥0∞) :
    uniformMeanENN (fun a => ∑' k, f a k) =
      ∑' k, uniformMeanENN (fun a => f a k) := by
  simp only [uniformMeanENN, div_eq_mul_inv]
  simp_rw [Finset.sum_mul, ← ENNReal.tsum_mul_right]
  rw [← tsum_fintype (L := SummationFilter.unconditional A), ENNReal.tsum_comm]
  simp only [tsum_fintype]

theorem meanENN_survival_prefix [Fintype V] (q m k : ℕ) (hV : 2 ≤ Fintype.card V) :
    uniformMeanENN (fun x : EdgeTuple V m =>
      ENNReal.ofReal (survival q (tupleGraph x) k)) =
    ENNReal.ofReal (processSurvival (V := V) q (m+k)) := by
  classical
  have hpair : Nonempty (Pair V) := by
    let a : V := Classical.choice (Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V))
    obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) a
    refine ⟨⟨s(a,b), ?_⟩⟩
    intro v hv
    have hh := Sym2.eq_iff.mp hv
    rcases hh with ⟨hav, hbv⟩ | ⟨hav, hbv⟩ <;> exact hba (hbv.trans hav.symm)
  calc
    _ = uniformMeanENN (fun x : EdgeTuple V m =>
        uniformMeanENN (fun y : EdgeTuple V k =>
          if Colorable q (tupleGraph x + tupleGraph y) then (1 : ℝ≥0∞) else 0)) := by
      congr 1
      funext x
      simpa [survival] using
        (ofReal_uniformProb_indicator
          (P := fun y : EdgeTuple V k => Colorable q (tupleGraph x + tupleGraph y)))
    _ = uniformMeanENN (fun z : EdgeTuple V (m+k) =>
        if Colorable q (tupleGraph z) then (1 : ℝ≥0∞) else 0) := by
      simpa [tupleGraph_append] using
        (uniformMeanENN_append (E := Pair V) (m := m) (k := k)
          (F := fun z : Fin (m+k) → Pair V =>
            if Colorable q (tupleGraph z) then (1 : ℝ≥0∞) else 0)).symm
    _ = ENNReal.ofReal (processSurvival (V := V) q (m+k)) := by
      symm
      simpa [processSurvival, survival] using
        (ofReal_uniformProb_indicator
          (P := fun z : EdgeTuple V (m+k) => Colorable q (tupleGraph z)))

theorem S3_28bStatement_holds : ThLean.BP.S3.S3_28bStatement := by
  intro V _ q hq hV m
  change uniformMeanENN (fun x : EdgeTuple V m =>
      ∑' k : ℕ, ENNReal.ofReal (survival q (tupleGraph x) k)) = _
  rw [uniformMeanENN_tsum_comm]
  apply tsum_congr
  intro k
  exact meanENN_survival_prefix (V := V) q m k hV

example : ThLean.BP.S3.S3_28bStatement := S3_28bStatement_holds

end ThLean.W.S387

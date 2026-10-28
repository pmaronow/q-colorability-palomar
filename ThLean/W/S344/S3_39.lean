import ThLean.BP.S3.Poisson

noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S344

open ThresholdFoundations
open ThLean.BP.S3
universe u

theorem S3_39Statement_of_deps
    (h03b : ThLean.BP.S3.S3_03bStatement.{u, u})
    (h31 : ThLean.BP.S3.S3_31Statement)
    (h32 : ThLean.BP.S3.S3_32Statement.{u}) :
    ThLean.BP.S3.S3_39Statement.{u} := by
  classical
  intro V instV hV h
  refine ⟨?_, ?_⟩
  · change Measurable (fun t : ℝ =>
      ∑' k : ℕ, ENNReal.ofReal (poissonWeight t k) *
        uniformMeanENN (fun x : EdgeTuple V k => h (tupleGraph x)))
    apply Measurable.ennreal_tsum
    intro k
    have hc : Continuous (fun t : ℝ => poissonWeight t k) := by
      simp only [poissonWeight]
      fun_prop
    exact (ENNReal.measurable_ofReal.comp hc.measurable).mul_const _
  · refine ⟨?_, ?_⟩
    · intro p
      have hm : Measurable (fun t : ℝ => poissonGraphMeanENN t h) := by
        change Measurable (fun t : ℝ =>
          ∑' k : ℕ, ENNReal.ofReal (poissonWeight t k) *
            uniformMeanENN (fun x : EdgeTuple V k => h (tupleGraph x)))
        apply Measurable.ennreal_tsum
        intro k
        have hc : Continuous (fun t : ℝ => poissonWeight t k) := by
          simp only [poissonWeight]
          fun_prop
        exact (ENNReal.measurable_ofReal.comp hc.measurable).mul_const _
      exact hm.comp (measurable_const.mul measurable_id)
    · refine ⟨?_, ?_⟩
      · intro t ht
        -- The list and tuple presentations are the same finite product law.
        classical
        let E := Pair V
        let ν : E → ℝ := fun _ => 1 / (Fintype.card E : ℝ)
        have hE : Nonempty E := by
          obtain ⟨a⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
          have hb : ∃ b : V, b ≠ a := by
            by_contra hn
            have hall : ∀ b : V, b = a := by
              intro b
              by_contra hba
              exact hn ⟨b, hba⟩
            have hcard : Fintype.card V ≤ 1 :=
              Fintype.card_le_one_iff.mpr (fun x y => (hall x).trans (hall y).symm)
            omega
          obtain ⟨b, hab⟩ := hb
          exact ⟨⟨s(a,b), by
            intro v hv
            rcases Sym2.eq_iff.mp hv with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · exact hab (hb.trans ha.symm)
            · exact hab (hb.trans ha.symm)⟩⟩
        have hcardE : 0 < Fintype.card E := Fintype.card_pos_iff.mpr hE
        have hν : ThLean.BP.S3.IsProbabilityVector ν := by
          constructor
          · intro e
            dsimp [ν]
            positivity
          · simp only [ν, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            field_simp [ne_of_gt (show (Fintype.card E : ℝ) > 0 by exact_mod_cast hcardE)]
        rcases h32 E ν t hν ht with ⟨_, _, _, hformula⟩
        have hweight (m : ℕ) (x : Fin m → E) :
            ENNReal.ofReal (poissonListMass t ν (List.ofFn x)) =
              ENNReal.ofReal (poissonWeight t m) *
                (Fintype.card (Fin m → E) : ℝ≥0∞)⁻¹ := by
          rw [hformula]
          rw [ENNReal.ofReal_mul ((h31 t ht).1 m)]
          rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hν.1 (x i))]
          have hone : ENNReal.ofReal (1 / (Fintype.card E : ℝ)) =
              (Fintype.card E : ℝ≥0∞)⁻¹ := by
            rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num)]
            simp only [ENNReal.ofReal_one, one_mul]
            rw [ENNReal.ofReal_inv_of_pos]
            · simp
            · exact_mod_cast hcardE
          simp_rw [ν, hone]
          rw [Fintype.card_fun]
          simp [Finset.prod_const, Fintype.card_fin, Nat.cast_pow, ENNReal.inv_pow]
        have hcount : ∀ (m : ℕ) (x : Fin m → E) (e : Sym2 V),
            List.countP (fun p : E => decide (p.val = e)) (List.ofFn x) =
              ∑ i : Fin m, if (x i).val = e then 1 else 0 := by
          intro m
          induction m with
          | zero => intro x e; simp
          | succ m ih =>
            intro x e
            rw [List.ofFn_succ, List.countP_cons]
            rw [ih (fun i => x i.succ) e]
            rw [Fin.sum_univ_succ]
            simp only [decide_eq_true_eq]
            omega
        have hgraph (m : ℕ) (x : Fin m → E) :
            listGraph (List.ofFn x) = tupleGraph x := by
          classical
          ext e
          rw [listGraph, ← List.countP_eq_length_filter]
          rw [hcount]
          rw [tupleGraph, Finset.card_eq_sum_ones, ← Finset.sum_filter]
        have hlen (m : ℕ) :
            (∑' x : Fin m → E,
              ENNReal.ofReal (poissonListMass t ν (List.ofFn x)) *
                h (listGraph (List.ofFn x))) =
              ENNReal.ofReal (poissonWeight t m) *
                uniformMeanENN (fun x : EdgeTuple V m => h (tupleGraph x)) := by
          rw [tsum_fintype]
          simp_rw [hweight m, hgraph m]
          rw [uniformMeanENN, div_eq_mul_inv]
          calc
            (∑ x : Fin m → E,
              (ENNReal.ofReal (poissonWeight t m) *
                (Fintype.card (Fin m → E) : ℝ≥0∞)⁻¹) * h (tupleGraph x)) =
              (∑ x : Fin m → E,
                ENNReal.ofReal (poissonWeight t m) * h (tupleGraph x)) *
                  (Fintype.card (Fin m → E) : ℝ≥0∞)⁻¹ := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro x hx
                    simp [mul_assoc, mul_left_comm, mul_comm]
            _ = ENNReal.ofReal (poissonWeight t m) *
                ((∑ x : Fin m → E, h (tupleGraph x)) *
                  (Fintype.card (Fin m → E) : ℝ≥0∞)⁻¹) := by
                    rw [← Finset.mul_sum]
                    ac_rfl
        have hlist :
            poissonListMeanENN t ν (fun w => h (listGraph w)) =
              ∑' m : ℕ, ∑' x : Fin m → E,
                ENNReal.ofReal (poissonListMass t ν (List.ofFn x)) *
                  h (listGraph (List.ofFn x)) := by
          unfold poissonListMeanENN
          calc
            (∑' xs : List E,
              ENNReal.ofReal (poissonListMass t ν xs) * h (listGraph xs)) =
              ∑' s : (Σ m : ℕ, Fin m → E),
                ENNReal.ofReal (poissonListMass t ν (List.ofFn s.2)) *
                  h (listGraph (List.ofFn s.2)) := by
                    symm
                    exact (List.equivSigmaTuple.symm).tsum_eq
                      (fun xs : List E =>
                        ENNReal.ofReal (poissonListMass t ν xs) * h (listGraph xs))
            _ = ∑' m : ℕ, ∑' x : Fin m → E,
                ENNReal.ofReal (poissonListMass t ν (List.ofFn x)) *
                  h (listGraph (List.ofFn x)) := ENNReal.tsum_sigma' _
        change poissonListMeanENN t ν (fun w => h (listGraph w)) =
          poissonMixtureENN t
            (fun m => uniformMeanENN (fun x : EdgeTuple V m => h (tupleGraph x)))
        rw [hlist]
        unfold poissonMixtureENN
        apply tsum_congr
        intro m
        exact hlen m
      · intro t π ht
        change poissonMixtureENN t
          (fun m => uniformMeanENN (fun x : EdgeTuple V m => h (relabel π (tupleGraph x)))) =
          poissonMixtureENN t
            (fun m => uniformMeanENN (fun x : EdgeTuple V m => h (tupleGraph x)))
        rcases h03b V V hV with ⟨_, _, hrel⟩
        unfold poissonMixtureENN
        congr 1
        funext m
        apply congrArg (fun a : ℝ≥0∞ => ENNReal.ofReal (poissonWeight t m) * a)
        change graphMeanENN m (fun G => h (relabel π G)) = graphMeanENN m h
        exact hrel π m h

example (h03b : ThLean.BP.S3.S3_03bStatement.{u, u})
    (h31 : ThLean.BP.S3.S3_31Statement)
    (h32 : ThLean.BP.S3.S3_32Statement.{u}) :
    ThLean.BP.S3.S3_39Statement.{u} := S3_39Statement_of_deps h03b h31 h32

end ThLean.W.S344

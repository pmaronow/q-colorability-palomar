module

public import ThLean.W.S390S.Discrete

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S390S
open ThresholdFoundations ThLean.BP.S3
universe u v
set_option maxHeartbeats 1000000

def listArrayEquiv (A : Type u) (B : Type v) :
    (A → List B) ≃ (Σ k : A → ℕ, (a : A) → Fin (k a) → B) where
  toFun xs := ⟨fun a => (xs a).length, fun a => (xs a).get⟩
  invFun p := fun a => List.ofFn (p.2 a)
  left_inv xs := by funext a; exact List.ofFn_get (xs a)
  right_inv p := by
    rcases p with ⟨k,x⟩
    apply Sigma.ext (by simp)
    apply Function.hfunext rfl
    intro a b hab
    cases eq_of_heq hab
    apply Function.hfunext (by simp)
    intro i j hij
    apply heq_of_eq
    change (List.ofFn (x a)).get i = x a j
    rw [List.get_ofFn]
    congr 1
    apply Fin.ext
    simpa using (Fin.val_eq_val_of_heq hij)

theorem uniformListMass_ofFn {B : Type v} [Fintype B] [Nonempty B]
    (h31 : S3_31Statement) (z : ℝ) (hz : 0 ≤ z) (k : ℕ) (x : Fin k → B) :
    ENNReal.ofReal (poissonListMass z (fun _ : B => 1 / (Fintype.card B : ℝ))
      (List.ofFn x)) =
        ENNReal.ofReal (poissonWeight z k) / Fintype.card (Fin k → B) := by
  have hc : 0 < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [poissonListMass, List.length_ofFn]
  rw [ENNReal.ofReal_mul ((h31 z hz).1 k)]
  have hm : ((List.ofFn x).map (fun _ : B => 1 / (Fintype.card B : ℝ))).prod =
      (1 / (Fintype.card B : ℝ)) ^ k := by
    simp [Function.comp_def, List.ofFn_const]
  rw [hm, ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.ofReal_div_of_pos hc]
  simp [Fintype.card_fun, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow]

theorem independentLists_atoms {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [Nonempty B] (h31 : S3_31Statement) (z : ℝ) (hz : 0 ≤ z)
    (f : (A → List B) → ℝ≥0∞) :
    independentPoissonListsMeanENN z f =
      ∑' xs : A → List B,
        (∏ a, ENNReal.ofReal (poissonListMass z
          (fun _ : B => 1 / (Fintype.card B : ℝ)) (xs a))) * f xs := by
  classical
  symm
  rw [← (listArrayEquiv A B).symm.tsum_eq, ENNReal.tsum_sigma']
  unfold independentPoissonListsMeanENN
  apply tsum_congr
  intro k
  dsimp only [listArrayEquiv, Equiv.coe_fn_symm_mk]
  simp_rw [uniformListMass_ofFn h31 z hz]
  rw [ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.natCast_ne_top _)]
  have hc : (Fintype.card ((a : A) → Fin (k a) → B) : ℝ≥0∞) =
      ∏ a : A, (Fintype.card (Fin (k a) → B) : ℝ≥0∞) := by
    rw [Fintype.card_pi, Nat.cast_prod]
  rw [← hc, tsum_fintype]
  unfold uniformMeanENN
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ac_rfl

theorem uniformListMass_nonneg {B : Type v} [Fintype B]
    (h31 : S3_31Statement) (z : ℝ) (hz : 0 ≤ z) (xs : List B) :
    0 ≤ poissonListMass z (fun _ : B => 1 / (Fintype.card B : ℝ)) xs := by
  unfold poissonListMass
  apply mul_nonneg ((h31 z hz).1 _)
  apply List.prod_nonneg
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  positivity

end ThLean.W.S390S

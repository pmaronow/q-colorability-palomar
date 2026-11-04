module

public import ThLean.BP.S3.Poisson

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u
set_option maxHeartbeats 800000

namespace ThLean.W.S333

open ThLean.BP.S3 ThresholdFoundations

private theorem tuple_product_sum_eq_one
    (E : Type u) [Fintype E] (ν : E → ℝ) (hν : IsProbabilityVector ν)
    (k : ℕ) :
    (∑ x : Fin k → E, ∏ i, ν (x i)) = 1 := by
  rw [← Fintype.prod_sum (fun _ : Fin k => fun e : E => ν e)]
  simp [hν.2]

private theorem poisson_list_tuple_sum
    (E : Type u) [Fintype E] (ν : E → ℝ) (hν : IsProbabilityVector ν)
    (z : ℝ) (k : ℕ) :
    (∑' x : Fin k → E, poissonListMass z ν (List.ofFn x)) = poissonWeight z k := by
  have hprod : (∑ x : Fin k → E, ∏ i, ν (x i)) = 1 :=
    tuple_product_sum_eq_one E ν hν k
  calc
    (∑' x : Fin k → E, poissonListMass z ν (List.ofFn x)) =
        ∑ x : Fin k → E, poissonWeight z k * ∏ i, ν (x i) := by
      simp [poissonListMass, List.length_ofFn, List.map_ofFn, List.prod_ofFn]
    _ = poissonWeight z k * ∑ x : Fin k → E, ∏ i, ν (x i) := by
      rw [← Finset.mul_sum]
    _ = poissonWeight z k := by rw [hprod, mul_one]

theorem S3_32Statement_of_deps
    (h31 : ThLean.BP.S3.S3_31Statement) :
    ThLean.BP.S3.S3_32Statement.{u} := by
  intro E _ _ ν z hν hz
  let f : (Σ k : ℕ, Fin k → E) → ℝ :=
    fun p => poissonListMass z ν (List.ofFn p.2)
  have hf_nonneg : ∀ p, 0 ≤ f p := by
    intro p
    have hw : 0 ≤ poissonWeight z p.1 := (h31 z hz).1 p.1
    have hprod : 0 ≤ ∏ i : Fin p.1, ν (p.2 i) :=
      Finset.prod_nonneg fun i _ => hν.1 (p.2 i)
    simpa only [f, poissonListMass, List.length_ofFn, List.map_ofFn, List.prod_ofFn,
      Function.comp_apply] using
      (mul_nonneg hw hprod)
  have hinner : ∀ k : ℕ, (∑' x : Fin k → E, f ⟨k, x⟩) = poissonWeight z k := by
    intro k
    simpa [f] using poisson_list_tuple_sum E ν hν z k
  have hfiber : ∀ k : ℕ, Summable (fun x : Fin k → E => f ⟨k, x⟩) := by
    intro k
    exact Summable.of_finite
  have houter : Summable (fun k : ℕ => ∑' x : Fin k → E, f ⟨k, x⟩) := by
    convert (h31 z hz).2.1 using 1
    funext k
    exact hinner k
  have hfsummable : Summable f :=
    (summable_sigma_of_nonneg hf_nonneg).2 ⟨hfiber, houter⟩
  have hequiv :
      (fun xs : List E => f (List.equivSigmaTuple xs)) = poissonListMass z ν := by
    funext xs
    change poissonListMass z ν (List.ofFn (List.equivSigmaTuple xs).2) = _
    exact congrArg (poissonListMass z ν) ((List.equivSigmaTuple (α := E)).left_inv xs)
  have hlist_summable : Summable (poissonListMass z ν) := by
    rw [← hequiv]
    exact (List.equivSigmaTuple (α := E)).summable_iff.mpr hfsummable
  have hlist_total : (∑' xs : List E, poissonListMass z ν xs) = 1 := by
    calc
      (∑' xs : List E, poissonListMass z ν xs) = ∑' p, f p := by
        calc
          (∑' xs : List E, poissonListMass z ν xs) =
              ∑' xs : List E, f (List.equivSigmaTuple xs) := by
            rw [hequiv]
          _ = ∑' p, f p := (List.equivSigmaTuple (α := E)).tsum_eq f
      _ = ∑' k : ℕ, poissonWeight z k := by
        rw [hfsummable.tsum_sigma]
        refine tsum_congr fun k => ?_
        exact hinner k
      _ = 1 := (h31 z hz).2.2.1
  have hlength : ∀ k : ℕ,
      (∑' xs : List E, if xs.length = k then poissonListMass z ν xs else 0) =
        poissonWeight z k := by
    intro k
    let g : (Σ n : ℕ, Fin n → E) → ℝ :=
      fun p => if p.1 = k then f p else 0
    have hg_nonneg : ∀ p, 0 ≤ g p := by
      intro p
      by_cases hp : p.1 = k
      · simp [g, hp, hf_nonneg]
      · simp [g, hp]
    have hg_le : ∀ p, g p ≤ f p := by
      intro p
      by_cases hp : p.1 = k
      · simp [g, hp]
      · simp [g, hp, hf_nonneg]
    have hgsummable : Summable g := Summable.of_nonneg_of_le hg_nonneg hg_le hfsummable
    have hginner : ∀ n : ℕ,
        (∑' x : Fin n → E, g ⟨n, x⟩) = if n = k then poissonWeight z n else 0 := by
      intro n
      by_cases hn : n = k
      · subst n
        simpa [g] using hinner k
      · simp [g, hn]
    calc
      (∑' xs : List E, if xs.length = k then poissonListMass z ν xs else 0) =
          ∑' p, g p := by
        calc
          (∑' xs : List E, if xs.length = k then poissonListMass z ν xs else 0) =
              ∑' xs : List E, g (List.equivSigmaTuple xs) := by
            refine tsum_congr fun xs => ?_
            simp [g, f, List.equivSigmaTuple]
          _ = ∑' p, g p := (List.equivSigmaTuple (α := E)).tsum_eq g
      _ = ∑' n : ℕ, if n = k then poissonWeight z n else 0 := by
        rw [hgsummable.tsum_sigma]
        exact tsum_congr hginner
      _ = poissonWeight z k := by
        rw [tsum_eq_single k]
        · simp
        · intro n hn
          simp [hn]
  refine ⟨hlist_summable, hlist_total, hlength, ?_⟩
  intro k x
  simp [poissonListMass, List.length_ofFn, List.map_ofFn, List.prod_ofFn]

end ThLean.W.S333

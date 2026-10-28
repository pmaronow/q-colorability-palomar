import ThLean.BP.S5.Poisson

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S557
open ThLean.BP.S5 ThresholdFoundations

theorem S5_14Statement_of_deps
    (h01 : ThLean.BP.S5.S5_E01Statement)
    (h05 : ThLean.BP.S5.S5_E05Statement) :
    ThLean.BP.S5.S5_14Statement := by
  intro a b ha hb hbBound z hz
  rcases h01.1 z hz with ⟨hw, hwSum, hgen, hbounded⟩
  have ha_le_one : ∀ i, a i ≤ 1 := by
    intro i
    have hprev : 0 ≤ ∑ k ∈ Finset.range i, a k := by
      apply Finset.sum_nonneg
      intro k hk
      exact ha k
    have hnext : b (i + 1) = (∑ k ∈ Finset.range i, a k) + a i := by
      rw [hb, Finset.sum_range_succ]
    have hbi := (hbBound (i + 1)).2
    rw [hnext] at hbi
    linarith
  have hsumA := (hbounded 1 a (by norm_num) (fun i => ⟨ha i, ha_le_one i⟩)).1
  have hsumB := (hbounded 1 b (by norm_num) hbBound).1
  have hmixA_nonneg := (hbounded 1 a (by norm_num) (fun i => ⟨ha i, ha_le_one i⟩)).2.1
  have hmixB_nonneg := (hbounded 1 b (by norm_num) hbBound).2.1
  have hc : 0 ≤ Real.exp z - 1 := by
    have := Real.add_one_le_exp z
    linarith
  let w : ℕ → ℝ := poissonWeight z
  let f : ℕ × ℕ → ℝ := fun p => if p.1 < p.2 then a p.1 * w p.2 else 0
  have hf_nonneg : ∀ p, 0 ≤ f p := by
    intro p
    by_cases hp : p.1 < p.2
    · simpa [f, hp] using mul_nonneg (ha p.1) ((hw p.2).1)
    · simp [f, hp]
  have htail : ∀ i, (∑' j, if i < j then w j else 0) ≤
      (Real.exp z - 1) * w i := by
    intro i
    have h := h05 z hz (i + 1) (by omega)
    simpa [w, Nat.succ_le_iff] using h
  have hrow_eq : ∀ i, (∑' j, f (i, j)) =
      a i * (∑' j, if i < j then w j else 0) := by
    intro i
    have hfun : (fun j => f (i, j)) = fun j => a i * (if i < j then w j else 0) := by
      funext j
      by_cases hij : i < j <;> simp [f, hij]
    rw [hfun, tsum_mul_left]
  have hrow_nonneg : ∀ i, 0 ≤ ∑' j, f (i, j) := by
    intro i
    exact tsum_nonneg fun j => hf_nonneg (i, j)
  have hrow_bound : ∀ i, (∑' j, f (i, j)) ≤
      (Real.exp z - 1) * (w i * a i) := by
    intro i
    rw [hrow_eq i]
    calc
      a i * (∑' j, if i < j then w j else 0) ≤
          a i * ((Real.exp z - 1) * w i) :=
        mul_le_mul_of_nonneg_left (htail i) (ha i)
      _ = (Real.exp z - 1) * (w i * a i) := by ring
  have hmajor : Summable (fun i => (Real.exp z - 1) * (w i * a i)) := by
    simpa only [mul_assoc] using hsumA.mul_left (Real.exp z - 1)
  have hrows : Summable (fun i => ∑' j, f (i, j)) :=
    Summable.of_nonneg_of_le (fun i => hrow_nonneg i) (hrow_bound) hmajor
  have hwSummable : Summable w := by simpa [w] using hwSum.summable
  have hinner_summable : ∀ i, Summable (fun j => f (i, j)) := by
    intro i
    refine Summable.of_nonneg_of_le
      (f := fun j => a i * w j) (g := fun j => f (i, j)) ?_ ?_ ?_
    · intro j
      exact hf_nonneg (i, j)
    · intro j
      by_cases hij : i < j
      · simp [f, hij]
      · simp [f, hij]
        exact mul_nonneg (ha i) (hw j).1
    · exact hwSummable.mul_left (a i)
  have hdouble : Summable f :=
    (summable_prod_of_nonneg hf_nonneg).2 ⟨hinner_summable, hrows⟩
  have hfinite_inner : ∀ j, (∑' i, f (i, j)) = w j * b j := by
    intro j
    rw [tsum_eq_sum (s := Finset.range j) (fun i hi => by
      have hij : j ≤ i := by simpa using hi
      simp [f, not_lt.mpr hij])]
    rw [hb j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i < j := Finset.mem_range.mp hi
    simp [f, hij, w, mul_comm]
  have hlhs_change : (∑' j, w j * b j) = ∑' i, ∑' j, f (i, j) := by
    calc
      (∑' j, w j * b j) = ∑' j, ∑' i, f (i, j) := by
        apply tsum_congr
        intro j
        rw [hfinite_inner j]
      _ = ∑' i, ∑' j, f (i, j) := by
        exact Summable.tsum_comm hdouble
  have hbound := Summable.tsum_le_tsum hrow_bound hrows hmajor
  have hfinal : (∑' i, ∑' j, f (i, j)) ≤
      (Real.exp z - 1) * (∑' i, w i * a i) := by
    calc
      (∑' i, ∑' j, f (i, j)) ≤ ∑' i, (Real.exp z - 1) * (w i * a i) := hbound
      _ = (Real.exp z - 1) * (∑' i, w i * a i) := tsum_mul_left
  refine ⟨hsumA, hsumB, ?_⟩
  change (∑' j, poissonWeight z j * b j) ≤
    (Real.exp z - 1) * (∑' i, poissonWeight z i * a i)
  simpa [w, poissonMixture] using hlhs_change.trans_le hfinal

end ThLean.W.S557

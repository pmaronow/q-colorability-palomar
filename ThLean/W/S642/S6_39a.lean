import ThLean.BP.S6.Descent

open scoped BigOperators

namespace ThLean.W.S642

theorem S6_39aStatement_holds : ThLean.BP.S6.S6_39aStatement := by
  intro M D a
  let J : Finset ℕ := Finset.Ico (D + 1) M
  let T : ℕ → Finset ℕ := fun m => J.filter (fun j => j ≤ m)
  let U : ℕ → Finset ℕ := fun j => (Finset.range M).filter (fun m => j ≤ m)
  have hleft (m : ℕ) (hm : m ∈ Finset.range M) :
      Finset.Ico (D + 1) (m + 1) = T m := by
    have hmM : m < M := Finset.mem_range.mp hm
    ext j
    simp only [T, J, Finset.mem_Ico, Finset.mem_filter]
    omega
  have hright (j : ℕ) (hj : j ∈ J) :
      Finset.Ico j M = U j := by
    ext m
    simp only [U, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at *
    omega
  calc
    (∑ m ∈ Finset.range M, ∑ j ∈ Finset.Ico (D + 1) (m + 1), a m j) =
        ∑ m ∈ Finset.range M, ∑ j ∈ T m, a m j := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [hleft m hm]
    _ = ∑ m ∈ Finset.range M, ∑ j ∈ J, (if j ≤ m then a m j else 0) := by
          apply Finset.sum_congr rfl
          intro m hm
          simp only [T, Finset.sum_filter]
    _ = ∑ j ∈ J, ∑ m ∈ Finset.range M, (if j ≤ m then a m j else 0) := by
          exact Finset.sum_comm
    _ = ∑ j ∈ J, ∑ m ∈ U j, a m j := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [U, Finset.sum_filter]
    _ = ∑ j ∈ Finset.Ico (D + 1) M, ∑ m ∈ Finset.Ico j M, a m j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hright j hj]

end ThLean.W.S642

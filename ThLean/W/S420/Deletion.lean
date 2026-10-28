import ThLean.BP.S4.Deletion

noncomputable section
open scoped BigOperators

namespace ThLean.W.S420

open ThLean.BP.S4
open ThresholdFoundations

theorem S4_RED_07Statement_of_deps
    (h : ThLean.BP.S4.S4_RED_06Statement) :
    ThLean.BP.S4.S4_RED_07Statement := by
  classical
  intro q n hq hn L U hLU
  let g : ℕ → ℝ := fun k =>
    uniformMean (fun x : EdgeTuple (Fin n) k =>
      kappa q (tupleGraph x) * deletionWeight q (U-k) (tupleGraph x))
  have hfilter (i : Fin U) :
      Finset.Ico (max i.val L) U =
        (Finset.Ico L U).filter (fun k => i.val ≤ k) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_filter]
    omega
  calc
    (∑ i : Fin U, uniformMean (fun x : EdgeTuple (Fin n) U =>
      ((deletionYMinus q L i x : ℝ)-(deletionY q L x : ℝ))^2)) =
        ∑ i : Fin U, ∑ k ∈ Finset.Ico (max i.val L) U, g k := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [g] using h q n hq hn L U hLU i
    _ = ∑ i : Fin U, ∑ k ∈ Finset.Ico L U,
          (if i.val ≤ k then g k else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfilter i, Finset.sum_filter]
    _ = ∑ k ∈ Finset.Ico L U, ∑ i : Fin U,
          (if i.val ≤ k then g k else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Ico L U, ((k+1 : ℕ) : ℝ) * g k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkU : k < U := (Finset.mem_Ico.mp hk).2
      have hcount :
          ∑ i : Fin U, (if i.val ≤ k then (1 : ℝ) else 0) = ((k+1 : ℕ) : ℝ) := by
        have hset : (Finset.range U).filter (fun i => i ≤ k) = Finset.range (k+1) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        calc
          (∑ i : Fin U, (if i.val ≤ k then (1 : ℝ) else 0)) =
              ∑ i ∈ Finset.range U, (if i ≤ k then (1 : ℝ) else 0) :=
            Fin.sum_univ_eq_sum_range (fun i : ℕ => if i ≤ k then (1 : ℝ) else 0) U
          _ = ∑ i ∈ (Finset.range U).filter (fun i => i ≤ k), (1 : ℝ) := by
            rw [← Finset.sum_filter]
          _ = ∑ i ∈ Finset.range (k+1), (1 : ℝ) := by rw [hset]
          _ = ((k+1 : ℕ) : ℝ) := by simp
      calc
        (∑ i : Fin U, (if i.val ≤ k then g k else 0)) =
            (∑ i : Fin U, (if i.val ≤ k then (1 : ℝ) else 0)) * g k := by
          calc
            (∑ i : Fin U, (if i.val ≤ k then g k else 0)) =
                ∑ i : Fin U, (if i.val ≤ k then (1 : ℝ) else 0) * g k := by
              apply Finset.sum_congr rfl
              intro i hi
              split_ifs <;> simp
            _ = (∑ i : Fin U, (if i.val ≤ k then (1 : ℝ) else 0)) * g k := by
              rw [Finset.sum_mul]
        _ = ((k+1 : ℕ) : ℝ) * g k := by rw [hcount]
    _ = ∑ k ∈ Finset.Ico L U, (k+1 : ℕ) *
          uniformMean (fun x : EdgeTuple (Fin n) k =>
            kappa q (tupleGraph x) * deletionWeight q (U-k) (tupleGraph x)) := by
      simp [g]

end ThLean.W.S420

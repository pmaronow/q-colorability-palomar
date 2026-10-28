import ThLean.BP.S4.Deletion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S419

open ThresholdFoundations
open ThLean.BP.S4

private theorem uniformMean_congr {A : Type*} [Fintype A] (f g : A → ℝ)
    (h : ∀ x, f x = g x) : uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl (fun x _ => h x)

private theorem uniformMean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun x => f x + g x) = uniformMean f + uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_add_distrib]
  ring

private theorem uniformMean_const_mul {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun x => c * f x) = c * uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

private theorem uniformMean_sum {A ι : Type*} [Fintype A] (s : Finset ι)
    (f : ι → A → ℝ) :
    uniformMean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, uniformMean (f i) := by
  classical
  unfold uniformMean
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

private theorem loopless_tupleGraph {n k : ℕ} (x : EdgeTuple (Fin n) k) :
    Loopless (tupleGraph x) := by
  intro v
  unfold tupleGraph
  apply Finset.card_eq_zero.mpr
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
  simpa using (x i).property v

/-- RED-06 from the square expansion, the two-time and diagonal deletion laws,
and the guarded lifetime-weight identity. -/
theorem S4_RED_06Statement_of_deps
    (h02 : ThLean.BP.S4.S4_RED_02Statement)
    (h04A : ThLean.BP.S4.S4_RED_04AStatement)
    (h04B : ThLean.BP.S4.S4_RED_04BStatement)
    (h05 : ThLean.BP.S4.S4_RED_05Statement) :
    ThLean.BP.S4.S4_RED_06Statement := by
  intro q n hq hn L U hLU i
  let S : Finset ℕ := Finset.Icc (max (i.val + 1) (L + 1)) U
  let f : ℕ → ℝ := fun k =>
    uniformMean (fun x : EdgeTuple (Fin n) k =>
      kappa q (tupleGraph x) * deletionWeight q (U-k) (tupleGraph x))
  have hExpand :
      uniformMean (fun x : EdgeTuple (Fin n) U =>
        ((deletionYMinus q L i x : ℝ) - (deletionY q L x : ℝ))^2) =
      ∑ m ∈ S, uniformMean (fun x : EdgeTuple (Fin n) U =>
        indicator (deletionDisagreement q x i m) +
          2 * ∑ l ∈ Finset.Icc (m+1) U,
            indicator (deletionDisagreement q x i m ∧
              Colorable q (deletedPrefix x i l))) := by
    have hfun :
        (fun x : EdgeTuple (Fin n) U =>
          ((deletionYMinus q L i x : ℝ) - (deletionY q L x : ℝ))^2) =
        fun x => ∑ m ∈ S,
          (indicator (deletionDisagreement q x i m) +
            2 * ∑ l ∈ Finset.Icc (m+1) U,
              indicator (deletionDisagreement q x i m ∧
                Colorable q (deletedPrefix x i l))) := by
      funext x
      exact h02 q n hq hn L U hLU i x
    rw [hfun]
    exact uniformMean_sum S (fun m x =>
      indicator (deletionDisagreement q x i m) +
        2 * ∑ l ∈ Finset.Icc (m+1) U,
          indicator (deletionDisagreement q x i m ∧
            Colorable q (deletedPrefix x i l)))
  have hterm (m : ℕ) (hm : m ∈ S) :
      uniformMean (fun x : EdgeTuple (Fin n) U =>
        indicator (deletionDisagreement q x i m) +
          2 * ∑ l ∈ Finset.Icc (m+1) U,
            indicator (deletionDisagreement q x i m ∧
              Colorable q (deletedPrefix x i l))) = f (m-1) := by
    have hmlo : max (i.val+1) (L+1) ≤ m := (Finset.mem_Icc.mp hm).1
    have hmu : m ≤ U := (Finset.mem_Icc.mp hm).2
    have him : i.val < m := by omega
    have hmpos : 1 ≤ m := by omega
    calc
      _ = uniformMean (fun x : EdgeTuple (Fin n) U =>
            indicator (deletionDisagreement q x i m)) +
          2 * ∑ l ∈ Finset.Icc (m+1) U,
            uniformMean (fun x : EdgeTuple (Fin n) U =>
              indicator (deletionDisagreement q x i m ∧
                Colorable q (deletedPrefix x i l))) := by
          rw [uniformMean_add, uniformMean_const_mul, uniformMean_sum]
      _ = uniformMean (fun y : EdgeTuple (Fin n) (m-1) =>
            kappa q (tupleGraph y)) +
          2 * ∑ l ∈ Finset.Icc (m+1) U,
            uniformMean (fun y : EdgeTuple (Fin n) (m-1) =>
              kappa q (tupleGraph y) * survival q (tupleGraph y) (l-m)) := by
          apply congrArg₂ (· + ·)
          · exact h04B q n hq hn U m i him hmu
          · apply congrArg (fun z : ℝ => 2*z)
            apply Finset.sum_congr rfl
            intro l hl
            have hlm : m ≤ l := by
              have := (Finset.mem_Icc.mp hl).1
              omega
            have hlu : l ≤ U := (Finset.mem_Icc.mp hl).2
            have htwo := h04A q n hq hn U m l i him hlm hlu (fun _ => 1)
            calc
              uniformMean (fun x : EdgeTuple (Fin n) U =>
                  indicator (deletionDisagreement q x i m ∧
                    Colorable q (deletedPrefix x i l))) =
                uniformMean (fun x : EdgeTuple (Fin n) U =>
                  indicator (deletionDisagreement q x i m) *
                    indicator (Colorable q (deletedPrefix x i l))) := by
                apply uniformMean_congr
                intro x
                by_cases hd : deletionDisagreement q x i m
                · by_cases hc : Colorable q (deletedPrefix x i l) <;>
                    simp [indicator, hd, hc]
                · simp [indicator, hd]
              _ = uniformMean (fun y : EdgeTuple (Fin n) (m-1) =>
                    kappa q (tupleGraph y) * survival q (tupleGraph y) (l-m)) := by
                simpa [one_mul] using htwo
      _ = uniformMean (fun y : EdgeTuple (Fin n) (m-1) =>
            kappa q (tupleGraph y) *
              (1 + 2 * ∑ l ∈ Finset.Icc (m+1) U,
                survival q (tupleGraph y) (l-m))) := by
          rw [← uniformMean_sum, ← uniformMean_const_mul, ← uniformMean_add]
          apply uniformMean_congr
          intro y
          rw [← Finset.mul_sum]
          ring
      _ = f (m-1) := by
          apply uniformMean_congr
          intro y
          rcases h05 q n hq hn m U hmpos hmu (tupleGraph y)
              (loopless_tupleGraph y) with
            ⟨_, _, _, hweight, _⟩
          have hb : U+1-m = U-(m-1) := by omega
          simpa [f, hb] using hweight.symm
  have hstart : max (i.val+1) (L+1) = max i.val L + 1 := by omega
  calc
    uniformMean (fun x : EdgeTuple (Fin n) U =>
      ((deletionYMinus q L i x : ℝ) - (deletionY q L x : ℝ))^2) =
        ∑ m ∈ S, f (m-1) := by
          rw [hExpand]
          apply Finset.sum_congr rfl
          intro m hm
          exact hterm m hm
    _ = ∑ k ∈ Finset.Ico (max i.val L) U, f k := by
          rw [show S = Finset.Icc (max i.val L + 1) U from by
            simp [S, hstart]]
          rw [← Finset.Ico_add_one_right_eq_Icc]
          simpa [f] using
            (Finset.sum_Ico_add_right_sub_eq
              (f := f) (max i.val L) U 1)

end ThLean.W.S419

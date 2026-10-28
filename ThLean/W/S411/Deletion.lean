import ThLean.BP.S4.Deletion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S411
open ThresholdFoundations

private theorem prop_of_later {P : ℕ → Prop}
    (hmono : ∀ k, P (k + 1) → P k) : ∀ a b, a ≤ b → P b → P a := by
  intro a b hab hb
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact hb
  | succ b ih =>
      by_cases h : a = b + 1
      · simpa [h] using hb
      · have hab' : a ≤ b := by omega
        exact ih hab' (hmono b hb)

private theorem clipped_count_identity (P : ℕ → Prop)
    (hmono : ∀ k, P (k + 1) → P k) :
    ∀ M L U : ℕ, L ≤ U → U ≤ M →
      min U (max L (∑ k ∈ Finset.range M, if P (k + 1) then 1 else 0)) =
        L + ∑ m ∈ Finset.Icc (L + 1) U, if P m then 1 else 0 := by
  intro M
  induction M with
  | zero =>
      intro L U hLU hUM
      have hL : L = 0 := by omega
      have hU : U = 0 := by omega
      subst L
      subst U
      simp
  | succ M ih =>
      intro L U hLU hUM
      by_cases hlast : P (M + 1)
      · have hcount :
          (∑ k ∈ Finset.range (M + 1), if P (k + 1) then 1 else 0) = M + 1 := by
          calc
            (∑ k ∈ Finset.range (M + 1), if P (k + 1) then 1 else 0) =
                ∑ _k ∈ Finset.range (M + 1), (1 : ℕ) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  have hk' : k + 1 ≤ M + 1 := by
                    have := Finset.mem_range.mp hk
                    omega
                  have hp : P (k + 1) := prop_of_later hmono (k + 1) (M + 1) hk' hlast
                  simp [hp]
            _ = M + 1 := by simp
        have hsum :
          (∑ m ∈ Finset.Icc (L + 1) U, if P m then 1 else 0) = U - L := by
          calc
            (∑ m ∈ Finset.Icc (L + 1) U, if P m then 1 else 0) =
                ∑ _m ∈ Finset.Icc (L + 1) U, (1 : ℕ) := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  have hmU : m ≤ U := (Finset.mem_Icc.mp hm).2
                  have hm' : m ≤ M + 1 := le_trans hmU hUM
                  have hp : P m := prop_of_later hmono m (M + 1) hm' hlast
                  simp [hp]
            _ = U - L := by
              simp [Nat.add_sub_cancel_left, hLU]
        rw [hcount, hsum]
        omega
      · let C : ℕ := ∑ k ∈ Finset.range M, if P (k + 1) then 1 else 0
        have hC : C ≤ M := by
          dsimp [C]
          calc
            (∑ k ∈ Finset.range M, if P (k + 1) then 1 else 0) ≤
                ∑ _k ∈ Finset.range M, (1 : ℕ) := by
                  apply Finset.sum_le_sum
                  intro k hk
                  split_ifs <;> omega
            _ = M := by simp
        have hcount :
            (∑ k ∈ Finset.range (M + 1), if P (k + 1) then 1 else 0) = C := by
          rw [Finset.sum_range_succ]
          simp [C, hlast]
        by_cases hL : L ≤ M
        · -- The endpoint U=M+1 contributes a final false term only.
          let U₀ := min U M
          have hLU₀ : L ≤ U₀ := by
            dsimp [U₀]
            exact Nat.le_min.mpr ⟨hLU, hL⟩
          have hU₀M : U₀ ≤ M := by dsimp [U₀]; exact min_le_right _ _
          have hsumU :
              (∑ m ∈ Finset.Icc (L + 1) U, if P m then 1 else 0) =
                ∑ m ∈ Finset.Icc (L + 1) U₀, if P m then 1 else 0 := by
            by_cases hU : U ≤ M
            · simp [U₀, Nat.min_eq_left hU]
            · have hUeq : U = M + 1 := by omega
              subst U
              dsimp [U₀]
              rw [Nat.min_eq_right (Nat.le_succ M)]
              calc
                (∑ m ∈ Finset.Icc (L + 1) (M + 1), if P m then 1 else 0) =
                    (∑ m ∈ Finset.Icc (L + 1) M, if P m then 1 else 0) +
                      (if P (M + 1) then 1 else 0) :=
                  Finset.sum_Icc_succ_top (by omega) _
                _ = _ := by simp [hlast]
          have hmax : max L C ≤ M := max_le hL hC
          have hmin : min U (max L C) = min U₀ (max L C) := by
            by_cases hU : U ≤ M
            · simp [U₀, Nat.min_eq_left hU]
            · have hUeq : U = M + 1 := by omega
              subst U
              have hU₀ : U₀ = M := by simp [U₀]
              rw [hU₀]
              calc
                min (M + 1) (max L C) = max L C := Nat.min_eq_right (by omega)
                _ = min M (max L C) := (Nat.min_eq_right hmax).symm
          rw [hcount, hmin, hsumU]
          exact ih L U₀ hLU₀ hU₀M
        · have hL' : L = M + 1 := by omega
          have hU' : U = M + 1 := by omega
          subst L
          subst U
          rw [hcount]
          simp [Finset.Icc_eq_empty_of_lt]

private theorem colorable_of_subgraph {V : Type*} {q : ℕ} {G F : MGraph V}
    (hGF : subgraph G F) (hF : Colorable q F) : Colorable q G := by
  rcases hF with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro u v huv
  exact hσ u v (lt_of_lt_of_le huv (hGF (s(u, v))))

private theorem tuplePrefix_subgraph {V : Type*} [Fintype V] {M : ℕ}
    (x : EdgeTuple V M) (m : ℕ) : subgraph (tuplePrefix x m) (tuplePrefix x (m + 1)) := by
  intro e
  unfold tuplePrefix
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rcases hi with ⟨him, he⟩
  exact ⟨by omega, he⟩

theorem S4_RED_01AStatement_holds : ThLean.BP.S4.S4_RED_01AStatement := by
  intro q n hq hn M L U hLU hUM x
  let P : ℕ → Prop := fun m => Colorable q (tuplePrefix x m)
  have hmono : ∀ k, P (k + 1) → P k := by
    intro k hk
    exact colorable_of_subgraph (tuplePrefix_subgraph x k) hk
  dsimp [clippedLast, cappedLast, P]
  exact clipped_count_identity P hmono M L U hLU hUM

example : ThLean.BP.S4.S4_RED_01AStatement := S4_RED_01AStatement_holds

end ThLean.W.S411

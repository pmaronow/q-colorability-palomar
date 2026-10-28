import ThLean.BP.S5.Poisson

noncomputable section
open scoped BigOperators

namespace ThLean.W.S556

open ThresholdFoundations
open ThLean.BP.S5

private theorem firstFailure_le_iff_of_step {P : ℕ → Prop}
    (hstep : ∀ n, P n → P (n + 1)) (j : ℕ) :
    firstFailure P ≤ (j : WithTop ℕ) ↔ P j := by
  classical
  unfold firstFailure
  split_ifs with hex
  · constructor
    · intro hle
      have hmin : Nat.find hex ≤ j := by exact_mod_cast hle
      have hbase : P (Nat.find hex) := Nat.find_spec hex
      have hiter : ∀ n, Nat.find hex ≤ n → P n := by
        intro n
        induction n with
        | zero =>
            intro hle
            have hz : Nat.find hex = 0 := by omega
            simpa [hz] using hbase
        | succ n ih =>
            intro hle
            by_cases hle' : Nat.find hex ≤ n
            · exact hstep n (ih hle')
            · have heq : Nat.find hex = n + 1 := by omega
              simpa [heq] using hbase
      exact hiter j hmin
    · intro hj
      have hmin : Nat.find hex ≤ j := Nat.find_min' hex hj
      exact_mod_cast hmin
  · constructor
    · intro hle
      simp at hle
    · intro hj
      exact False.elim (hex ⟨j, hj⟩)

private theorem firstFailure_pos_of_not_zero {P : ℕ → Prop}
    (hzero : ¬ P 0) : (1 : WithTop ℕ) ≤ firstFailure P := by
  classical
  unfold firstFailure
  split_ifs with hex
  · have hne : Nat.find hex ≠ 0 := by
      intro h
      have hz : Nat.find hex = 0 := h
      exact hzero (hz ▸ Nat.find_spec hex)
    have hpos : 1 ≤ Nat.find hex := Nat.one_le_iff_ne_zero.mpr hne
    exact_mod_cast hpos
  · simp

private theorem addedRoot_colorable_prefix_of_succ
    (h01 : S5_01AStatement) (V : Type) [Fintype V] (q : ℕ) (hq : 3 ≤ q)
    (B : MGraph V) (x : ℕ → V) (n : ℕ)
    (hcol : Colorable q (addRoot B
      (List.ofFn (fun i : Fin (n + 1) => x i.val)))) :
    Colorable q (addRoot B (List.ofFn (fun i : Fin n => x i.val))) := by
  rcases hcol with ⟨τ, hτ⟩
  rcases (h01 V q hq B
    (List.ofFn (fun i : Fin (n + 1) => x i.val)) τ).1 hτ with
      ⟨hbase, hconstraints⟩
  have hlong : ∀ i : Fin (n + 1), τ none ≠ τ (some (x i.val)) := by
    simpa only [List.forall_mem_ofFn_iff] using hconstraints
  refine ⟨τ, (h01 V q hq B
    (List.ofFn (fun i : Fin n => x i.val)) τ).2 ⟨hbase, ?_⟩⟩
  simpa only [List.forall_mem_ofFn_iff, Fin.val_castSucc] using
    (fun i : Fin n => hlong i.castSucc)

private theorem addedRoot_colorable_empty
    (h01 : S5_01AStatement) (V : Type) [Fintype V] (q : ℕ) (hq : 3 ≤ q)
    (B : MGraph V) (hB : Colorable q B) : Colorable q (addRoot B []) := by
  rcases hB with ⟨σ, hσ⟩
  let τ : Option V → Fin q := fun v => v.elim ⟨0, by omega⟩ σ
  refine ⟨τ, ?_⟩
  exact (h01 V q hq B [] τ).2 ⟨hσ, by simp⟩

theorem S5_13AStatement_of_deps
    (h01 : S5_01AStatement) : S5_13AStatement := by
  intro V _ q hq B x hB
  let P : ℕ → Prop := fun j =>
    ¬ Colorable q (addRoot B (List.ofFn (fun i : Fin j => x i.val)))
  have hzero : ¬ P 0 := by
    simp only [P, not_not]
    exact addedRoot_colorable_empty h01 V q hq B hB
  have hstep : ∀ j, P j → P (j + 1) := by
    intro j hj
    change ¬ Colorable q (addRoot B
      (List.ofFn (fun i : Fin (j + 1) => x i.val)))
    intro hcol
    exact hj (addedRoot_colorable_prefix_of_succ h01 V q hq B x j hcol)
  constructor
  · change (1 : WithTop ℕ) ≤ firstFailure P
    exact firstFailure_pos_of_not_zero hzero
  · intro j
    change firstFailure P ≤ (j : WithTop ℕ) ↔ P j
    exact firstFailure_le_iff_of_step hstep j

end ThLean.W.S556

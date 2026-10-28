import ThLean.BP.SA.Tree

noncomputable section

namespace ThLean.W.SA60

theorem SA_T34Statement_holds : ThLean.BP.SA.SA_T34Statement := by
  classical
  intro h hh m j
  let lo : ℕ := Nat.ceil ((j : ℝ) / h)
  let hi : ℕ := Nat.ceil (((j + 1 : ℕ) : ℝ) / h)
  let k : ℕ := Nat.ceil (1 / h)
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (Nat.le_succ j)
    · exact hh.le
  have hhibound : hi ≤ lo + k := by
    dsimp [hi, lo, k]
    apply Nat.ceil_le.mpr
    calc
      (((j + 1 : ℕ) : ℝ) / h) = ((j : ℝ) + 1) / h := by norm_cast
      _ = (j : ℝ) / h + 1 / h := by ring
      _ ≤ (Nat.ceil ((j : ℝ) / h) : ℝ) + (Nat.ceil (1 / h) : ℝ) :=
        add_le_add (Nat.le_ceil _) (Nat.le_ceil _)
      _ = ((Nat.ceil ((j : ℝ) / h) + Nat.ceil (1 / h) : ℕ) : ℝ) := by norm_cast
  let s : Finset ℝ := (Finset.image Nat.cast (Finset.Icc (1 : ℕ) m)).filter
    (fun x : ℝ => Nat.floor (x * h) = j)
  have hs_sub : s ⊆ (Finset.Ico lo hi).image Nat.cast := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxbase, hbucket⟩
    change x ∈ Finset.image Nat.cast (Finset.Icc (1 : ℕ) m) at hxbase
    rcases Finset.mem_image.mp hxbase with ⟨i, him, rfl⟩
    have hfloor : (j : ℝ) ≤ (i : ℝ) * h ∧ (i : ℝ) * h < (j : ℝ) + 1 :=
      (Nat.floor_eq_iff (mul_nonneg (by positivity : 0 ≤ (i : ℝ)) hh.le)).mp hbucket
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_Ico.mpr ?_, rfl⟩
    constructor
    · dsimp [lo]
      apply Nat.ceil_le.mpr
      rw [div_le_iff₀ hh]
      simpa [mul_comm] using hfloor.1
    · dsimp [hi]
      apply Nat.lt_ceil.mpr
      rw [lt_div_iff₀ hh]
      simpa [Nat.cast_add, Nat.cast_one] using hfloor.2
  have hcard : s.card ≤ k + 1 := calc
    s.card ≤ ((Finset.Ico lo hi).image Nat.cast).card := Finset.card_le_card hs_sub
    _ ≤ (Finset.Ico lo hi).card := Finset.card_image_le
    _ = hi - lo := by simp
    _ ≤ k := by omega
    _ ≤ k + 1 := Nat.le_add_right k 1
  simpa [s, k] using hcard

end ThLean.W.SA60

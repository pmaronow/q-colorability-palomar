import ThLean.BP.S5.Completion

noncomputable section
open scoped BigOperators

namespace ThLean.W.S501
open ThLean.BP.S5
open ThresholdFoundations

theorem S5_27Statement_holds : ThLean.BP.S5.S5_27Statement := by
  intro V _ _ D hD
  have hcard : Fintype.card (UniformSubset V D) = (Fintype.card V).choose D := by
    simp [UniformSubset]
  have hchoose : 0 < (Fintype.card V).choose D := Nat.choose_pos hD
  have htrans : ∀ Z Z' : UniformSubset V D,
      ∃ π : Equiv.Perm V, permSubset D π Z = Z' := by
    intro Z Z'
    obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq Z.val Z'.val (by
      rw [Z.property, Z'.property])
    refine ⟨π, ?_⟩
    apply Subtype.ext
    exact hπ
  refine ⟨hcard, hchoose, htrans, ?_⟩
  intro μ hnonneg hsum hinvariant Z
  have hconst : ∀ Z' : UniformSubset V D, μ Z' = μ Z := by
    intro Z'
    obtain ⟨π, hπ⟩ := htrans Z Z'
    have hinv := hinvariant π Z
    have heq : permSubset D π Z = Z' := hπ
    rw [heq] at hinv
    exact hinv
  have hsumConst : (∑ Z' : UniformSubset V D, μ Z') = 1 := hsum
  have hsumOne : (∑ Z' : UniformSubset V D, μ Z) = 1 := by
    calc
      (∑ Z' : UniformSubset V D, μ Z) = ∑ Z' : UniformSubset V D, μ Z' := by
        apply Finset.sum_congr rfl
        intro Z' _
        exact (hconst Z').symm
      _ = 1 := hsumConst
  have hmul : (Fintype.card (UniformSubset V D) : ℝ) * μ Z = 1 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsumOne
  have hden : (Fintype.card (UniformSubset V D) : ℝ) ≠ 0 := by
    rw [hcard]
    exact_mod_cast hchoose.ne'
  have hmul' : μ Z * (Fintype.card (UniformSubset V D) : ℝ) = 1 := by
    nlinarith [hmul]
  calc
    μ Z = 1 / (Fintype.card (UniformSubset V D) : ℝ) := (eq_div_iff hden).2 hmul'
    _ = 1 / ((Fintype.card V).choose D : ℝ) := by rw [hcard]

end ThLean.W.S501

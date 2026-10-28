import ThLean.Contrib.S549.PoissonSplit

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S549
open ThresholdFoundations ThLean.BP.S5

theorem S5_09AStatement_of_08B_and_count_factorization
    (h08b : S5_08BStatement)
    (hfactor : ThLean.Contrib.S549.S549_CountMeanPartitionFactorizationStatement) :
    ThLean.BP.S5.S5_09AStatement := by
  classical
  intro V _ hCard Z hZ hOutside t ht f hf
  let A := {v : V // v ∈ Z}
  let B := {v : V // v ∉ Z}
  let toV : A ⊕ B → V := Sum.elim Subtype.val Subtype.val
  let fromV : V → A ⊕ B := fun v =>
    if hv : v ∈ Z then Sum.inl ⟨v, hv⟩ else Sum.inr ⟨v, hv⟩
  have hleft : Function.LeftInverse toV fromV := by
    intro v
    by_cases hv : v ∈ Z <;> simp [toV, fromV, hv]
  have hright : Function.RightInverse toV fromV := by
    intro x
    cases x with
    | inl a => simp [toV, fromV, a.property]
    | inr b => simp [toV, fromV, b.property]
  have hbij : Function.Bijective toV := ⟨hright.injective, hleft.surjective⟩
  let e : A ⊕ B ≃ V := Equiv.ofBijective toV hbij
  have hcardB : Fintype.card B = Fintype.card V - Z.card := by
    simp [B]
  have hB : 2 ≤ Fintype.card B := by rw [hcardB]; exact hOutside
  let r : ℝ := t / ((Fintype.card V).choose 2 : ℝ)
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hpoisson : poissonGraphMean t f = countMean r f := by
    simpa [r] using h08b V (by omega) t ht f hf
  have h := hfactor V A B e hCard hB r hr f hf
  rw [hpoisson]
  simpa [r, A, B, e, toV] using h

example (h08b : S5_08BStatement)
    (hfactor : ThLean.Contrib.S549.S549_CountMeanPartitionFactorizationStatement) :
    ThLean.BP.S5.S5_09AStatement :=
  S5_09AStatement_of_08B_and_count_factorization h08b hfactor

end ThLean.W.S549

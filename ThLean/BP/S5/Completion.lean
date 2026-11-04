module

public import ThLean.BP.S5.Identification

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S5
open ThresholdFoundations

/-- P3-LOW-27; eq:low-completion: symmetry characterizes the uniform subset law. -/
def S5_27Statement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (D : ℕ), D ≤ Fintype.card V →
    Fintype.card (UniformSubset V D) = (Fintype.card V).choose D ∧
    0 < (Fintype.card V).choose D ∧
    (∀ Z Z' : UniformSubset V D, ∃ π : Equiv.Perm V, permSubset D π Z = Z') ∧
    (∀ μ : UniformSubset V D → ℝ,
      (∀ Z, 0 ≤ μ Z) → (∑ Z, μ Z) = 1 →
      (∀ (π : Equiv.Perm V) Z, μ (permSubset D π Z) = μ Z) →
      ∀ Z, μ Z = 1 / ((Fintype.card V).choose D : ℝ))

/-- P3-LOW-28A; eq:low-completion: count and normalize support completions. -/
def S5_28AStatement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (D : ℕ), 1 ≤ D → D ≤ Fintype.card V →
  ∀ x : Fin D → V,
    let xs := List.ofFn x
    0 < (Fintype.card V - xs.toFinset.card).choose (D - xs.toFinset.card) ∧
    Fintype.card (CompletionSubset xs D) =
      (Fintype.card V - xs.toFinset.card).choose (D - xs.toFinset.card) ∧
    (∑ Z : UniformSubset V D, completionKernel D xs Z) = 1 ∧
    (∀ Z, 0 ≤ completionKernel D xs Z) ∧
    (∀ Z, 0 < completionKernel D xs Z → xs.toFinset ⊆ Z.val)

/-- P3-LOW-28B; eq:low-completion: equivariance and the uniform subset marginal. -/
def S5_28BStatement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (D : ℕ), 1 ≤ D → D ≤ Fintype.card V →
    (∀ (π : Equiv.Perm V) (x : Fin D → V) (Z : UniformSubset V D),
      completionKernel D (List.ofFn (π ∘ x)) (permSubset D π Z) =
        completionKernel D (List.ofFn x) Z) ∧
    (∀ Z : UniformSubset V D,
      uniformMean (fun x : Fin D → V => completionKernel D (List.ofFn x) Z) =
        1 / (Fintype.card (UniformSubset V D) : ℝ))

/-- P3-LOW-28; eq:low-completion: normalized explicit completion coupling. -/
def S5_28Statement : Prop := S5_28AStatement ∧ S5_28BStatement

theorem S5_28_assembly (ha : S5_28AStatement) (hb : S5_28BStatement) :
    S5_28Statement := ⟨ha, hb⟩

/-- P3-LOW-29A; finite-kernel comparison used in eq:low-completion. -/
def S5_29AStatement : Prop :=
  ∀ (A B : Type) [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (K : A → B → ℝ),
    (∀ a b, 0 ≤ K a b) → (∀ a, (∑ b, K a b) = 1) →
    (∀ b, uniformMean (fun a => K a b) = 1 / (Fintype.card B : ℝ)) →
    ∀ (f : A → ℝ) (g : B → ℝ),
    (∀ a b, 0 < K a b → f a ≤ g b) → uniformMean f ≤ uniformMean g

/-- P3-LOW-29; eq:low-completion: iid-list obstruction is bounded by identification. -/
def S5_29Statement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (q D : ℕ),
    3 ≤ q → 1 ≤ D → D ≤ Fintype.card V →
    ∀ B : MGraph V, Loopless B →
      nmProbability q D B ≤ identificationFailureProbability q D B

theorem S5_29_assembly (h05 : S5_05Statement) (h27 : S5_27Statement)
    (h28 : S5_28Statement) (ha : S5_29AStatement) : S5_29Statement := by
  intro V _ _ q D hq hD hDV B _
  have hcard := h27 V D hDV
  have hpos : 0 < Fintype.card (UniformSubset V D) := by
    rw [hcard.1]
    exact hcard.2.1
  have : Nonempty (UniformSubset V D) := Fintype.card_pos_iff.mp hpos
  have h := ha (Fin D → V) (UniformSubset V D)
    (fun x Z => completionKernel D (List.ofFn x) Z)
    (fun x => (h28.1 V D hD hDV x).2.2.2.1)
    (fun x => (h28.1 V D hD hDV x).2.2.1)
    (h28.2 V D hD hDV).2
    (fun x => indicator (neverMonochromatic q B (List.ofFn x)))
    (fun Z => indicator (Colorable q B ∧ ¬ Colorable q (identify B Z.val)))
  apply h
  intro x Z hK
  by_cases hnm : neverMonochromatic q B (List.ofFn x)
  · have hsub := (h28.1 V D hD hDV x).2.2.2.2 Z hK
    have hne : Z.val.Nonempty := Finset.card_pos.mp (by omega)
    have hf := (h05 V q hq).2.2 B (List.ofFn x) Z.val hnm hsub hne
    simp [indicator, hnm, hnm.1, hf]
  · simp only [indicator, hnm, ite_false]
    split_ifs <;> norm_num

end ThLean.BP.S5

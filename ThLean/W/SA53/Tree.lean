module

public import ThLean.BP.SA.Tree

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA53

open ThLean.BP.SA

theorem SA_T30Statement_holds : SA_T30Statement := by
  intro ℓ n hℓ hn
  let q : ℕ := n / ℓ
  let r : ℕ := n % ℓ
  have hℓpos : 0 < ℓ := by omega
  have hq : ℓ ≤ q := by
    dsimp [q]
    rw [Nat.le_div_iff_mul_le hℓpos]
    simpa [pow_two] using hn
  have hr : r < ℓ := by
    dsimp [r]
    exact Nat.mod_lt n hℓpos
  have hrq : r ≤ q := le_trans hr.le hq
  have hdiv : n = q * ℓ + r := by
    dsimp [q, r]
    exact (Nat.div_add_mod' n ℓ).symm
  let b : List ℕ := List.replicate (q - r) ℓ ++ List.replicate r (ℓ + 1)
  refine ⟨hdiv, hq, hr, b, ?_, ?_, ?_, ?_, ?_⟩
  · simp [b, q, r, Nat.sub_add_cancel hrq]
  · calc
      b.sum = (q - r) * ℓ + r * (ℓ + 1) := by
        simp [b, List.sum_replicate]
      _ = (q - r + r) * ℓ + r := by
        simp [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.add_assoc]
      _ = q * ℓ + r := by rw [Nat.sub_add_cancel hrq]
      _ = n := hdiv.symm
  · simp [b, q, r, List.count_append, List.count_replicate]
  · simp [b, q, r, List.count_append, List.count_replicate]
  · intro x hx
    simp only [b, List.mem_append, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

end ThLean.W.SA53

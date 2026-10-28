import ThLean.BP.S3.Cycles

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S360
open ThresholdFoundations

private theorem sum_nat_le_one_cases {α : Type u} [Fintype α] (f : α → ℕ)
    (h : (∑ a, f a) ≤ 1) :
    (∀ a, f a = 0) ∨ ∃ a, f a = 1 ∧ ∀ b, b ≠ a → f b = 0 := by
  classical
  by_cases hzero : (∑ a, f a) = 0
  · left
    intro a
    have hle : f a ≤ ∑ x, f x :=
      Finset.single_le_sum (fun x hx => Nat.zero_le (f x)) (Finset.mem_univ a)
    omega
  · right
    obtain ⟨a, ha, hfa⟩ := Finset.exists_ne_zero_of_sum_ne_zero hzero
    have hle : f a ≤ ∑ x, f x :=
      Finset.single_le_sum (fun x hx => Nat.zero_le (f x)) (Finset.mem_univ a)
    have hfaone : f a = 1 := by omega
    refine ⟨a, hfaone, ?_⟩
    intro b hba
    have hdecomp : f a + (∑ x ∈ Finset.univ.erase a, f x) = ∑ x, f x := by
      simpa using Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)
    have hrest : (∑ x ∈ Finset.univ.erase a, f x) = 0 := by
      have hdecomp' : 1 + (∑ x ∈ Finset.univ.erase a, f x) = ∑ x, f x := by
        simpa [hfaone] using hdecomp
      omega
    have hbmem : b ∈ Finset.univ.erase a := by simp [hba]
    have hble : f b ≤ ∑ x ∈ Finset.univ.erase a, f x :=
      Finset.single_le_sum (fun x hx => Nat.zero_le (f x)) hbmem
    omega

/-- The tree-plus-one-edge classification for a loopless multigraph. -/
theorem S3_57aStatement_holds : ThLean.BP.S3.S3_57aStatement := by
  classical
  intro V _ K T hK htree hTcount hKcount
  rcases htree with ⟨hTloop, hsub, _, _⟩
  let excess : Sym2 V → ℕ := fun e => K e - T e
  have hcount : edgeCount K = edgeCount T + (∑ e, excess e) := by
    unfold edgeCount
    calc
      (∑ e, K e) = ∑ e, (T e + excess e) := by
        apply Finset.sum_congr rfl
        intro e he
        dsimp [excess]
        calc
          K e = (K e - T e) + T e := (Nat.sub_add_cancel (hsub e)).symm
          _ = T e + (K e - T e) := Nat.add_comm _ _
      _ = (∑ e, T e) + ∑ e, excess e := Finset.sum_add_distrib
  have hexcess : (∑ e, excess e) ≤ 1 := by
    rw [hcount] at hKcount
    omega
  rcases sum_nat_le_one_cases excess hexcess with hzero | ⟨e, he, hother⟩
  · left
    apply funext
    intro x
    have hx := hzero x
    dsimp [excess] at hx
    have hTx := hsub x
    omega
  · right
    have hnotdiag : ∀ v : V, e ≠ s(v, v) := by
      intro v hev
      have hde : excess e = 0 := by
        simp [excess, hev, hK v, hTloop v]
      rw [he] at hde
      omega
    have hval : K e = T e + 1 := by
      dsimp [excess] at he
      have hTe := hsub e
      omega
    refine ⟨⟨e, hnotdiag⟩, ?_⟩
    funext x
    change K x = Function.update T e (T e + 1) x
    by_cases hx : x = e
    · subst x
      simp [hval]
    · have hdx := hother x hx
      dsimp [excess] at hdx
      have hTx := hsub x
      have hxeq : K x = T x := by omega
      simp [hx, hxeq]

example : ThLean.BP.S3.S3_57aStatement := S3_57aStatement_holds

end ThLean.W.S360

import ThLean.W.SA51S.Means

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA51S
open ThresholdFoundations ThLean.BP.SA

def sumGraph {A B : Type} (G : MGraph A) (H : MGraph B) : MGraph (A ⊕ B) :=
  Sym2.lift ⟨fun x y => match x, y with
    | .inl a, .inl b => G s(a,b)
    | .inr a, .inr b => H s(a,b)
    | _, _ => 0,
    by intro x y; cases x <;> cases y <;> simp [Sym2.eq_swap]⟩

@[simp] lemma sumGraph_ll {A B : Type} (G : MGraph A) (H : MGraph B) (a b : A) :
    sumGraph G H s(Sum.inl a, Sum.inl b) = G s(a,b) := rfl

@[simp] lemma sumGraph_rr {A B : Type} (G : MGraph A) (H : MGraph B) (a b : B) :
    sumGraph G H s(Sum.inr a, Sum.inr b) = H s(a,b) := rfl

@[simp] lemma sumGraph_lr {A B : Type} (G : MGraph A) (H : MGraph B) (a : A) (b : B) :
    sumGraph G H s(Sum.inl a, Sum.inr b) = 0 := rfl

@[simp] lemma sumGraph_rl {A B : Type} (G : MGraph A) (H : MGraph B) (a : B) (b : A) :
    sumGraph G H s(Sum.inr a, Sum.inl b) = 0 := rfl

lemma sumGraph_add_left {A B : Type} (G : MGraph A) (H : MGraph B) (a b : A) :
    sumGraph (addEdge G s(a,b)) H = addEdge (sumGraph G H) s(Sum.inl a, Sum.inl b) := by
  funext e
  induction e using Sym2.inductionOn with | _ x y =>
    cases x <;> cases y <;> simp [addEdge, Function.update_apply, Sym2.eq_iff]

lemma sumGraph_add_right {A B : Type} (G : MGraph A) (H : MGraph B) (a b : B) :
    sumGraph G (addEdge H s(a,b)) = addEdge (sumGraph G H) s(Sum.inr a, Sum.inr b) := by
  funext e
  induction e using Sym2.inductionOn with | _ x y =>
    cases x <;> cases y <;> simp [addEdge, Function.update_apply, Sym2.eq_iff]

def blockGraph {n₁ n₂ : ℕ} (G : MGraph (Fin n₁)) (H : MGraph (Fin n₂)) :
    MGraph (Fin (n₁+n₂)) := fun e => sumGraph G H (Sym2.map finSumFinEquiv.symm e)

lemma blockGraph_colorable (q n₁ n₂ : ℕ) (G : MGraph (Fin n₁)) (H : MGraph (Fin n₂)) :
    Colorable q (blockGraph G H) ↔ Colorable q G ∧ Colorable q H := by
  constructor
  · rintro ⟨σ, hσ⟩
    constructor
    · refine ⟨fun a => σ (finSumFinEquiv (Sum.inl a)), ?_⟩
      intro a b hab
      apply hσ _ _
      simpa [blockGraph] using hab
    · refine ⟨fun a => σ (finSumFinEquiv (Sum.inr a)), ?_⟩
      intro a b hab
      apply hσ _ _
      simpa [blockGraph] using hab
  · rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
    refine ⟨fun a => Sum.elim σ τ (finSumFinEquiv.symm a), ?_⟩
    intro a b hab
    change 0 < sumGraph G H s(finSumFinEquiv.symm a, finSumFinEquiv.symm b) at hab
    cases ha : finSumFinEquiv.symm a with
    | inl x =>
      cases hb : finSumFinEquiv.symm b with
      | inl y => simpa [ha, hb] using hσ x y (by simpa [ha, hb] using hab)
      | inr y => simp [ha, hb] at hab
    | inr x =>
      cases hb : finSumFinEquiv.symm b with
      | inl y => simp [ha, hb] at hab
      | inr y => simpa [ha, hb] using hτ x y (by simpa [ha, hb] using hab)

@[simp] lemma blockGraph_zero (n₁ n₂ : ℕ) :
    blockGraph (0 : MGraph (Fin n₁)) (0 : MGraph (Fin n₂)) = 0 := by
  funext e
  induction e using Sym2.inductionOn with | _ a b =>
    change sumGraph 0 0 s(finSumFinEquiv.symm a, finSumFinEquiv.symm b) = 0
    cases finSumFinEquiv.symm a <;> cases finSumFinEquiv.symm b <;> rfl

lemma blockGraph_add_left {n₁ n₂ : ℕ} (G : MGraph (Fin n₁)) (H : MGraph (Fin n₂))
    (a b : Fin n₁) : blockGraph (addEdge G s(a,b)) H =
      addEdge (blockGraph G H) s(leftVertex n₁ n₂ a, leftVertex n₁ n₂ b) := by
  funext e
  rw [blockGraph, sumGraph_add_left]
  have he : (Sym2.map finSumFinEquiv.symm e = s(Sum.inl a, Sum.inl b)) ↔
      e = s(leftVertex n₁ n₂ a, leftVertex n₁ n₂ b) := by
    simpa only [Sym2.map_mk, show leftVertex n₁ n₂ a =
      finSumFinEquiv (Sum.inl a) from rfl, show leftVertex n₁ n₂ b =
      finSumFinEquiv (Sum.inl b) from rfl, Equiv.symm_apply_apply] using
      (Sym2.map.injective finSumFinEquiv.symm.injective).eq_iff
        (a := e) (b := s(leftVertex n₁ n₂ a, leftVertex n₁ n₂ b))
  simp only [addEdge, Function.update_apply, he]
  simp [blockGraph, show leftVertex n₁ n₂ a = finSumFinEquiv (Sum.inl a) from rfl,
    show leftVertex n₁ n₂ b = finSumFinEquiv (Sum.inl b) from rfl]

lemma blockGraph_add_right {n₁ n₂ : ℕ} (G : MGraph (Fin n₁)) (H : MGraph (Fin n₂))
    (a b : Fin n₂) : blockGraph G (addEdge H s(a,b)) =
      addEdge (blockGraph G H) s(rightVertex n₁ n₂ a, rightVertex n₁ n₂ b) := by
  funext e
  rw [blockGraph, sumGraph_add_right]
  have he : (Sym2.map finSumFinEquiv.symm e = s(Sum.inr a, Sum.inr b)) ↔
      e = s(rightVertex n₁ n₂ a, rightVertex n₁ n₂ b) := by
    simpa only [Sym2.map_mk, show rightVertex n₁ n₂ a =
      finSumFinEquiv (Sum.inr a) from rfl, show rightVertex n₁ n₂ b =
      finSumFinEquiv (Sum.inr b) from rfl, Equiv.symm_apply_apply] using
      (Sym2.map.injective finSumFinEquiv.symm.injective).eq_iff
        (a := e) (b := s(rightVertex n₁ n₂ a, rightVertex n₁ n₂ b))
  simp only [addEdge, Function.update_apply, he]
  simp [blockGraph, show rightVertex n₁ n₂ a = finSumFinEquiv (Sum.inr a) from rfl,
    show rightVertex n₁ n₂ b = finSumFinEquiv (Sum.inr b) from rfl]

end ThLean.W.SA51S

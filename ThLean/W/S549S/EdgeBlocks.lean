import ThLean.W.S549S.ProductMean

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S549S
open ThresholdFoundations ThLean.BP.S5

abbrev EdgeBlocks (A B : Type) := Sym2 B ⊕ (Sym2 A ⊕ (A × B))

def sumEdge {A B : Type} : EdgeBlocks A B → Sym2 (A ⊕ B) :=
  Sum.elim (Sym2.map Sum.inr)
    (Sum.elim (Sym2.map Sum.inl) (fun p => s(Sum.inl p.1, Sum.inr p.2)))

lemma sumEdge_bijective (A B : Type) : Function.Bijective (@sumEdge A B) := by
  constructor
  · rintro (⟨⟨b₁, b₂⟩⟩ | (⟨⟨a₁, a₂⟩⟩ | ⟨a, b⟩))
      (⟨⟨b₃, b₄⟩⟩ | (⟨⟨a₃, a₄⟩⟩ | ⟨a', b'⟩)) h
    all_goals simp [sumEdge, Prod.ext_iff] at h ⊢ <;> exact h
  · intro q
    refine Sym2.ind (fun u v => ?_) q
    rcases u with a | b <;> rcases v with a' | b'
    · exact ⟨Sum.inr (Sum.inl s(a, a')), rfl⟩
    · exact ⟨Sum.inr (Sum.inr (a, b')), rfl⟩
    · exact ⟨Sum.inr (Sum.inr (a', b)), Sym2.eq_swap⟩
    · exact ⟨Sum.inl s(b, b'), rfl⟩

def sym2Equiv {U V : Type} (e : U ≃ V) : Sym2 U ≃ Sym2 V :=
  Equiv.ofBijective (Sym2.map e) ⟨Sym2.map.injective e.injective, by
    intro q
    refine ⟨Sym2.map e.symm q, ?_⟩
    induction q using Sym2.ind with
    | _ u v => simp⟩

def edgeEquiv {A B V : Type} (e : A ⊕ B ≃ V) : EdgeBlocks A B ≃ Sym2 V :=
  (Equiv.ofBijective sumEdge (sumEdge_bijective A B)).trans (sym2Equiv e)

@[simp] lemma edgeEquiv_outside {A B V : Type} (e : A ⊕ B ≃ V) (q : Sym2 B) :
    edgeEquiv e (Sum.inl q) = Sym2.map (fun b => e (Sum.inr b)) q := by
  induction q using Sym2.ind with
  | _ u v => rfl

@[simp] lemma edgeEquiv_inside {A B V : Type} (e : A ⊕ B ≃ V) (q : Sym2 A) :
    edgeEquiv e (Sum.inr (Sum.inl q)) = Sym2.map (fun a => e (Sum.inl a)) q := by
  induction q using Sym2.ind with
  | _ u v => rfl

@[simp] lemma edgeEquiv_crossing {A B V : Type} (e : A ⊕ B ≃ V) (p : A × B) :
    edgeEquiv e (Sum.inr (Sum.inr p)) = s(e (Sum.inl p.1), e (Sum.inr p.2)) := rfl

lemma diagonal_iff {U : Type} (u v : U) :
    (∃ a, s(u, v) = s(a, a)) ↔ u = v := by
  constructor
  · rintro ⟨a, h⟩
    rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    all_goals exact h₁.trans h₂.symm
  · rintro rfl
    exact ⟨u, rfl⟩

lemma perPairRate_pair {U : Type} (r : ℝ) (u v : U) :
    perPairRate r s(u, v) = if u = v then 0 else r := by
  classical
  rw [perPairRate, diagonal_iff]

lemma perPairRate_map {U V : Type} (r : ℝ) (f : U → V)
    (hf : Function.Injective f) (q : Sym2 U) :
    perPairRate r (Sym2.map f q) = perPairRate r q := by
  induction q using Sym2.ind with
  | _ u v =>
    change perPairRate r s(f u, f v) = perPairRate r s(u, v)
    rw [perPairRate_pair, perPairRate_pair, hf.eq_iff]

@[simp] lemma edgeEquiv_rate_outside {A B V : Type}
    (e : A ⊕ B ≃ V) (r : ℝ) (q : Sym2 B) :
    perPairRate r (edgeEquiv e (Sum.inl q)) = perPairRate r q := by
  rw [edgeEquiv_outside]
  exact perPairRate_map r _ (e.injective.comp Sum.inr_injective) q

@[simp] lemma edgeEquiv_rate_inside {A B V : Type}
    (e : A ⊕ B ≃ V) (r : ℝ) (q : Sym2 A) :
    perPairRate r (edgeEquiv e (Sum.inr (Sum.inl q))) = perPairRate r q := by
  rw [edgeEquiv_inside]
  exact perPairRate_map r _ (e.injective.comp Sum.inl_injective) q

@[simp] lemma edgeEquiv_rate_crossing {A B V : Type}
    (e : A ⊕ B ≃ V) (r : ℝ) (p : A × B) :
    perPairRate r (edgeEquiv e (Sum.inr (Sum.inr p))) = r := by
  have hne : e (Sum.inl p.1) ≠ e (Sum.inr p.2) := by simp
  rw [edgeEquiv_crossing, perPairRate_pair, ite_eq_right hne]

def assemble {A B V : Type} (e : A ⊕ B ≃ V)
    (GB : MGraph B) (GA : MGraph A) (c : A × B → ℕ) : MGraph V :=
  fun q => Sum.elim GB (Sum.elim GA c) ((edgeEquiv e).symm q)

lemma assemble_formula {A B V : Type} [Fintype A] [Fintype B] [Fintype V]
    (e : A ⊕ B ≃ V) (GB : MGraph B) (GA : MGraph A) (c : A × B → ℕ) :
    assemble e GB GA c =
      mapGraph (fun b => e (Sum.inr b)) GB + mapGraph (fun a => e (Sum.inl a)) GA +
        (fun q => ∑ p : A × B, if q = s(e (Sum.inl p.1), e (Sum.inr p.2))
          then c p else 0) := by
  classical
  funext q
  have hsum :
      (∑ k : EdgeBlocks A B,
        if edgeEquiv e k = q then Sum.elim GB (Sum.elim GA c) k else 0) =
      assemble e GB GA c q := by
    calc
      _ = ∑ u : Sym2 V, if u = q then assemble e GB GA c u else 0 := by
        apply Fintype.sum_equiv (edgeEquiv e)
        intro k
        simp [assemble]
      _ = _ := by simp
  rw [← hsum]
  simp [Fintype.sum_sum_type, mapGraph, eq_comm, add_assoc]
  rfl

end ThLean.W.S549S

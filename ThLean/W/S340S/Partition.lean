import ThLean.W.S339.Poisson

noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S3
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S340S
universe u

abbrev Outside {V : Type u} [Fintype V] (S : Finset V) :=
  {v : V // v ∈ Finset.univ \ S}

abbrev Inside {V : Type u} (S : Finset V) := {v : V // v ∈ S}

def liftPair {V : Type u} (S : Finset V) (p : Pair (Inside S)) : Pair V := by
  refine ⟨Sym2.map Subtype.val p.val, ?_⟩
  intro v hv
  have hd : (Sym2.map Subtype.val p.val).IsDiag := by
    rw [hv]
    exact Sym2.diag_isDiag v
  have hi : p.val.IsDiag := (Sym2.isDiag_map Subtype.val_injective).mp hd
  exact p.property (p.val.diagElem hi) (Sym2.diag_diagElem hi).symm

@[simp] theorem liftPair_val {V : Type u} (S : Finset V) (p : Pair (Inside S)) :
    (liftPair S p).val = Sym2.map Subtype.val p.val := rfl

theorem liftPair_injective {V : Type u} (S : Finset V) :
    Function.Injective (liftPair S) := by
  intro p q h
  apply Subtype.ext
  exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h)

theorem mem_liftPair {V : Type u} (S : Finset V) (p : Pair (Inside S))
    {v : V} (hv : v ∈ (liftPair S p).val) : v ∈ S := by
  obtain ⟨a, _, ha⟩ := Sym2.mem_map.mp hv
  exact ha ▸ a.property

def crossPair {V : Type u} [Fintype V] (S : Finset V)
    (a : Inside S) (b : Outside S) : Pair V := by
  refine ⟨s(a.val, b.val), ?_⟩
  intro v hv
  have hab : a.val ≠ b.val := by
    intro h
    exact (Finset.mem_sdiff.mp b.property).2 (h ▸ a.property)
  rcases Sym2.eq_iff.mp hv with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact hab (h₁.trans h₂.symm)
  · exact hab (h₁.trans h₂.symm)

@[simp] theorem crossPair_val {V : Type u} [Fintype V] (S : Finset V)
    (a : Inside S) (b : Outside S) : (crossPair S a b).val = s(a.val,b.val) := rfl

theorem crossPair_injective {V : Type u} [Fintype V] (S : Finset V) :
    Function.Injective (fun p : Inside S × Outside S => crossPair S p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hv := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp hv with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
  · exact False.elim ((Finset.mem_sdiff.mp d.property).2 (h₁ ▸ a.property))

abbrev SplitAlphabet {V : Type u} [Fintype V] (S : Finset V) :=
  Pair (Outside S) ⊕ (Pair (Inside S) ⊕ (Inside S × Outside S))

abbrev SplitIndex {V : Type u} [Fintype V] (S : Finset V) :=
  Pair (Outside S) ⊕ (Pair (Inside S) ⊕ Inside S)

def embedSplit {V : Type u} [Fintype V] (S : Finset V) : SplitAlphabet S → Pair V
  | .inl p => liftPair (Finset.univ \ S) p
  | .inr (.inl p) => liftPair S p
  | .inr (.inr p) => crossPair S p.1 p.2

theorem embedSplit_injective {V : Type u} [Fintype V] (S : Finset V) :
    Function.Injective (embedSplit S) := by
  have hBC (p : Pair (Outside S)) (q : Pair (Inside S)) :
      liftPair (Finset.univ \ S) p ≠ liftPair S q := by
    intro h
    have hex : ∃ a : Inside S, a.val ∈ Sym2.map Subtype.val q.val := by
      induction q.val using Sym2.ind with
      | h a b => exact ⟨a, by simp⟩
    obtain ⟨a,hm⟩ := hex
    change a.val ∈ (liftPair S q).val at hm
    rw [← h] at hm
    exact (Finset.mem_sdiff.mp (mem_liftPair _ _ hm)).2 a.property
  have hBX (p : Pair (Outside S)) (a : Inside S) (b : Outside S) :
      liftPair (Finset.univ \ S) p ≠ crossPair S a b := by
    intro h
    have hm : a.val ∈ (liftPair (Finset.univ \ S) p).val := by rw [h]; simp
    exact (Finset.mem_sdiff.mp (mem_liftPair _ _ hm)).2 a.property
  have hCX (p : Pair (Inside S)) (a : Inside S) (b : Outside S) :
      liftPair S p ≠ crossPair S a b := by
    intro h
    have hm : b.val ∈ (liftPair S p).val := by rw [h]; simp
    exact (Finset.mem_sdiff.mp b.property).2 (mem_liftPair _ _ hm)
  intro x y h
  rcases x with p | p | ⟨a,b⟩ <;> rcases y with q | q | ⟨c,d⟩
  · exact congrArg Sum.inl (liftPair_injective _ h)
  · exact False.elim (hBC p q h)
  · exact False.elim (hBX p c d h)
  · exact False.elim (hBC q p h.symm)
  · exact congrArg (Sum.inr ∘ Sum.inl) (liftPair_injective _ h)
  · exact False.elim (hCX p c d h)
  · exact False.elim (hBX q a b h.symm)
  · exact False.elim (hCX q a b h.symm)
  · exact congrArg (Sum.inr ∘ Sum.inr) (crossPair_injective S h)

theorem embedSplit_surjective {V : Type u} [Fintype V] (S : Finset V) :
    Function.Surjective (embedSplit S) := by
  rintro ⟨e,he⟩
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by intro h; subst b; exact he a rfl
    let mkPair (T : Finset V) (ha : a ∈ T) (hb : b ∈ T) : Pair (Inside T) :=
      ⟨s(⟨a,ha⟩,⟨b,hb⟩), by
        intro c hc
        have hd := Sym2.mk_isDiag_iff.mp (hc.symm ▸
          (show (s(c,c)).IsDiag from rfl))
        exact hab (congrArg Subtype.val hd)⟩
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · exact ⟨.inr (.inl (mkPair S ha hb)), Subtype.ext rfl⟩
    · exact ⟨.inr (.inr (⟨a,ha⟩,⟨b,by simp [hb]⟩)), Subtype.ext rfl⟩
    · refine ⟨.inr (.inr (⟨b,hb⟩,⟨a,by simp [ha]⟩)), ?_⟩
      apply Subtype.ext
      exact Sym2.eq_swap
    · exact ⟨.inl (mkPair _ (by simp [ha]) (by simp [hb])), Subtype.ext rfl⟩

def splitEquiv {V : Type u} [Fintype V] (S : Finset V) : SplitAlphabet S ≃ Pair V :=
  Equiv.ofBijective (embedSplit S) ⟨embedSplit_injective S, embedSplit_surjective S⟩

def collapseSplit {V : Type u} [Fintype V] (S : Finset V) : SplitAlphabet S → SplitIndex S
  | .inl p => .inl p
  | .inr (.inl p) => .inr (.inl p)
  | .inr (.inr p) => .inr (.inr p.1)

def blockLabel {V : Type u} [Fintype V] (S : Finset V) (e : Pair V) : SplitIndex S :=
  collapseSplit S ((splitEquiv S).symm e)

@[simp] theorem blockLabel_embed {V : Type u} [Fintype V] (S : Finset V)
    (x : SplitAlphabet S) : blockLabel S (embedSplit S x) = collapseSplit S x := by
  exact congrArg (collapseSplit S) ((splitEquiv S).symm_apply_apply x)

@[simp] theorem blockLabel_lift_out {V : Type u} [Fintype V] (S : Finset V)
    (p : Pair (Outside S)) : blockLabel S (liftPair (Finset.univ \ S) p) = .inl p :=
  blockLabel_embed S (.inl p)

@[simp] theorem blockLabel_lift_in {V : Type u} [Fintype V] (S : Finset V)
    (p : Pair (Inside S)) : blockLabel S (liftPair S p) = .inr (.inl p) :=
  blockLabel_embed S (.inr (.inl p))

@[simp] theorem blockLabel_cross {V : Type u} [Fintype V] (S : Finset V)
    (a : Inside S) (b : Outside S) : blockLabel S (crossPair S a b) = .inr (.inr a) :=
  blockLabel_embed S (.inr (.inr (a,b)))

theorem blockLabel_out_iff {V : Type u} [Fintype V] (S : Finset V)
    (e : Pair V) (p : Pair (Outside S)) :
    blockLabel S e = .inl p ↔ e = liftPair (Finset.univ \ S) p := by
  obtain ⟨x,rfl⟩ := embedSplit_surjective S e
  rw [blockLabel_embed]
  change collapseSplit S x = _ ↔ embedSplit S x = embedSplit S (.inl p)
  rw [(embedSplit_injective S).eq_iff]
  rcases x with q | q | ⟨a,b⟩ <;> simp [collapseSplit]

theorem blockLabel_in_iff {V : Type u} [Fintype V] (S : Finset V)
    (e : Pair V) (p : Pair (Inside S)) :
    blockLabel S e = .inr (.inl p) ↔ e = liftPair S p := by
  obtain ⟨x,rfl⟩ := embedSplit_surjective S e
  rw [blockLabel_embed]
  change collapseSplit S x = _ ↔ embedSplit S x = embedSplit S (.inr (.inl p))
  rw [(embedSplit_injective S).eq_iff]
  rcases x with q | q | ⟨a,b⟩ <;> simp [collapseSplit]

theorem blockLabel_cross_iff {V : Type u} [Fintype V] (S : Finset V)
    (e : Pair V) (a : Inside S) :
    blockLabel S e = .inr (.inr a) ↔ ∃ b : Outside S, e = crossPair S a b := by
  obtain ⟨x,rfl⟩ := embedSplit_surjective S e
  rw [blockLabel_embed]
  change collapseSplit S x = _ ↔ ∃ b, embedSplit S x = embedSplit S (.inr (.inr (a,b)))
  simp only [(embedSplit_injective S).eq_iff]
  rcases x with q | q | ⟨c,d⟩ <;> simp [collapseSplit, Prod.ext_iff]

theorem blockLabel_cross_iff_exists {V : Type u} [Fintype V] (S : Finset V)
    (e : Pair V) (a : Inside S) :
    blockLabel S e = .inr (.inr a) ↔
      ∃ v ∈ Finset.univ \ S, e.val = s(a.val,v) := by
  rw [blockLabel_cross_iff]
  constructor
  · rintro ⟨b,rfl⟩; exact ⟨b.val,b.property,rfl⟩
  · rintro ⟨v,hv,he⟩; exact ⟨⟨v,hv⟩,Subtype.ext he⟩

end ThLean.W.S340S

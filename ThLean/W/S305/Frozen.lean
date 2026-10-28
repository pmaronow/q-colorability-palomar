import ThLean.BP.S3.Graph

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v

namespace ThLean.W.S305
open ThresholdFoundations

private theorem uniformProb_mono {A : Type*} [Fintype A] (P Q : A → Prop)
    (h : ∀ a, P a → Q a) : uniformProb P ≤ uniformProb Q := by
  classical
  unfold uniformProb uniformMean
  have hsum : (∑ a, indicator (P a)) ≤ ∑ a, indicator (Q a) := by
    apply Finset.sum_le_sum
    intro a ha
    by_cases hp : P a
    · have hq := h a hp
      simp [indicator, hp, hq]
    · by_cases hq : Q a <;> simp [indicator, hp, hq]
  by_cases hc : Fintype.card A = 0
  · have hcR : (Fintype.card A : ℝ) = 0 := by exact_mod_cast hc
    simp [hcR]
  · have hcpos : (0 : ℝ) < (Fintype.card A : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    exact div_le_div_of_nonneg_right hsum (le_of_lt hcpos)

private theorem uniformProb_range {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProb P ∧ uniformProb P ≤ 1 := by
  classical
  unfold uniformProb uniformMean
  have hsum0 : 0 ≤ ∑ a, indicator (P a) :=
    Finset.sum_nonneg fun a _ => by
      unfold indicator
      split_ifs <;> norm_num
  have hsum1 : (∑ a, indicator (P a)) ≤ (Fintype.card A : ℝ) := by
    calc
      (∑ a, indicator (P a)) ≤ ∑ _a : A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        unfold indicator
        split_ifs <;> norm_num
      _ = (Fintype.card A : ℝ) := by simp
  by_cases hc : Fintype.card A = 0
  · have hcR : (Fintype.card A : ℝ) = 0 := by exact_mod_cast hc
    simp [hcR]
  · have hcpos : (0 : ℝ) < (Fintype.card A : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    constructor
    · exact div_nonneg hsum0 (le_of_lt hcpos)
    · calc
        (∑ a, indicator (P a)) / (Fintype.card A : ℝ) ≤
            (Fintype.card A : ℝ) / (Fintype.card A : ℝ) :=
          div_le_div_of_nonneg_right hsum1 (le_of_lt hcpos)
        _ = 1 := div_self (ne_of_gt hcpos)

private def pairRelabelEquiv {V W : Type*} (π : V ≃ W) : Pair V ≃ Pair W := by
  classical
  let f : Sym2 V → Sym2 W := Sym2.map π
  let g : Sym2 W → Sym2 V := Sym2.map π.symm
  have hfg (e : Sym2 V) : g (f e) = e := by
    change Sym2.map π.symm (Sym2.map π e) = e
    rw [Sym2.map_map]
    have hc : π.symm ∘ π = id := by
      funext x
      exact π.symm_apply_apply x
    rw [hc, Sym2.map_id]
    rfl
  have hgf (e : Sym2 W) : f (g e) = e := by
    change Sym2.map π (Sym2.map π.symm e) = e
    rw [Sym2.map_map]
    have hc : π ∘ π.symm = id := by
      funext x
      exact π.apply_symm_apply x
    rw [hc, Sym2.map_id]
    rfl
  refine
    { toFun := fun e => ⟨f e.val, ?_⟩
      invFun := fun e => ⟨g e.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro w hdiag
    have heq : e.val = s(π.symm w, π.symm w) := by
      calc
        e.val = g (f e.val) := (hfg e.val).symm
        _ = g (s(w, w)) := congrArg g hdiag
        _ = s(π.symm w, π.symm w) := by simp [g]
    exact e.property (π.symm w) heq
  · intro v hdiag
    have heq : e.val = s(π v, π v) := by
      calc
        e.val = f (g e.val) := (hgf e.val).symm
        _ = f (s(v, v)) := congrArg f hdiag
        _ = s(π v, π v) := by simp [f]
    exact e.property (π v) heq
  · intro e
    apply Subtype.ext
    exact hfg e.val
  · intro e
    apply Subtype.ext
    exact hgf e.val

private theorem uniformProb_pair_relabel {V W : Type*} [Fintype V] [Fintype W]
    (π : V ≃ W) (P : Pair W → Prop) :
    uniformProb P = uniformProb (fun e : Pair V => P (pairRelabelEquiv π e)) := by
  classical
  unfold uniformProb uniformMean
  rw [Fintype.card_congr (pairRelabelEquiv π)]
  rw [← Equiv.sum_comp (pairRelabelEquiv π) (fun e => indicator (P e))]

private theorem frozenPair_relabel_iff {V W : Type*} [Fintype V] [Fintype W]
    {q : ℕ} (π : V ≃ W) (G : MGraph V)
    (hf : ∀ a b, Frozen q (relabel π G) (π a) (π b) ↔ Frozen q G a b)
    (e : Pair V) :
    FrozenPair q (relabel π G) (pairRelabelEquiv π e) ↔ FrozenPair q G e := by
  constructor
  · rintro ⟨a, b, hval, hfr⟩
    have hval' : e.val = s(π.symm a, π.symm b) := by
      apply (Sym2.map.injective π.injective)
      calc
        Sym2.map π e.val = s(a, b) := hval
        _ = Sym2.map π (s(π.symm a, π.symm b)) := by simp
    refine ⟨π.symm a, π.symm b, hval', ?_⟩
    exact (hf (π.symm a) (π.symm b)).mp (by simpa using hfr)
  · rintro ⟨a, b, hval, hfr⟩
    refine ⟨π a, π b, ?_, ?_⟩
    · change Sym2.map π e.val = s(π a, π b)
      rw [hval]
      simp
    · exact (hf a b).mpr hfr

theorem S3_09bStatement_of_deps
    (h01 : ThLean.BP.S3.S3_01Statement.{u, v})
    (h09a : ThLean.BP.S3.S3_09aStatement.{u}) :
    ThLean.BP.S3.S3_09bStatement.{u, v} := by
  classical
  intro V W instV instW q hq
  rcases h01 V W q hq with ⟨_, _, _, hrel, _, _, _⟩

  have hColorRel (G : MGraph V) (π : V ≃ W) :
      Colorable q (relabel π G) ↔ Colorable q G := by
    constructor
    · rintro ⟨τ, hτ⟩
      refine ⟨τ ∘ π, ?_⟩
      have hcomp : (τ ∘ π) ∘ π.symm = τ := by
        funext w
        simp [Function.comp_apply]
      have hτ' : IsColoring q (relabel π G) ((τ ∘ π) ∘ π.symm) := by
        rw [hcomp]
        exact hτ
      exact (hrel G π (τ ∘ π)).mp hτ'
    · rintro ⟨σ, hσ⟩
      exact ⟨σ ∘ π.symm, (hrel G π σ).mpr hσ⟩

  have hFrozenRel (G : MGraph V) (π : V ≃ W) (a b : V) :
      Frozen q (relabel π G) (π a) (π b) ↔ Frozen q G a b := by
    change (Colorable q (relabel π G) ∧
      (∀ σ, IsColoring q (relabel π G) σ → σ (π a) = σ (π b))) ↔
      (Colorable q G ∧ (∀ σ, IsColoring q G σ → σ a = σ b))
    constructor
    · rintro ⟨hc, hsame⟩
      refine ⟨(hColorRel G π).mp hc, ?_⟩
      intro σ hσ
      have hσ' : IsColoring q (relabel π G) (σ ∘ π.symm) :=
        (hrel G π σ).mpr hσ
      have := hsame (σ ∘ π.symm) hσ'
      simpa using this
    · rintro ⟨hc, hsame⟩
      refine ⟨(hColorRel G π).mpr hc, ?_⟩
      intro τ hτ
      have hcomp : (τ ∘ π) ∘ π.symm = τ := by
        funext w
        simp [Function.comp_apply]
      have hτ' : IsColoring q (relabel π G) ((τ ∘ π) ∘ π.symm) := by
        rw [hcomp]
        exact hτ
      have hσ : IsColoring q G (τ ∘ π) := (hrel G π (τ ∘ π)).mp hτ'
      have := hsame (τ ∘ π) hσ
      simpa using this

  have hClassRel (G : MGraph V) (π : V ≃ W) (a : V) :
      frozenClass q (relabel π G) (π a) = (frozenClass q G a).image π := by
    ext w
    simp only [frozenClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hw
      refine ⟨π.symm w, ?_, π.apply_symm_apply w⟩
      have hw' : Frozen q (relabel π G) (π a) (π (π.symm w)) := by
        simpa using hw
      exact (hFrozenRel G π a (π.symm w)).mp hw'
    · rintro ⟨b, hb, rfl⟩
      exact (hFrozenRel G π a b).mpr hb

  have hsubColorable {G H : MGraph V} (hsub : subgraph G H)
      (hH : Colorable q H) : Colorable q G := by
    rcases hH with ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro a b hab
    exact hσ a b (lt_of_lt_of_le hab (hsub (s(a, b))))

  have hFrozenPersist {G H : MGraph V} (hsub : subgraph G H)
      (hH : Colorable q H) {a b : V} (hG : Frozen q G a b) : Frozen q H a b := by
    refine ⟨hH, ?_⟩
    intro σ hσ
    apply hG.2
    intro x y hxy
    exact hσ x y (lt_of_lt_of_le hxy (hsub (s(x, y))))

  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G H hsub hH
    have hG := hsubColorable hsub hH
    have hkp : ∀ e : Pair V, FrozenPair q G e → FrozenPair q H e := by
      intro e he
      rcases he with ⟨a, b, hv, hf⟩
      exact ⟨a, b, hv, hFrozenPersist hsub hH hf⟩
    refine ⟨hG, ?_, ?_, ?_⟩
    · intro a b hf
      exact hFrozenPersist hsub hH hf
    · intro a x hx
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hFrozenPersist hsub hH (Finset.mem_filter.mp hx).2⟩
    · exact uniformProb_mono _ _ hkp
  · intro G π a
    exact hClassRel G π a
  · intro G π
    refine ⟨?_, ?_⟩
    · have hpair : ∀ e : Pair V,
          FrozenPair q (relabel π G) (pairRelabelEquiv π e) ↔ FrozenPair q G e :=
        frozenPair_relabel_iff π G (hFrozenRel G π)
      unfold kappa
      rw [uniformProb_pair_relabel π (FrozenPair q (relabel π G))]
      unfold uniformProb uniformMean
      apply congrArg (fun z : ℝ => z / (Fintype.card (Pair V) : ℝ))
      apply Finset.sum_congr rfl
      intro e he
      simp [indicator, hpair e]
    · by_cases hc : Colorable q G
      · have hselfG : ∀ a, a ∈ frozenClass q G a :=
          (h09a V q hq G hc).2.1
        have hselfRel : ∀ w, w ∈ frozenClass q (relabel π G) w := by
          intro w
          have hs := hselfG (π.symm w)
          have hsF : Frozen q G (π.symm w) (π.symm w) :=
            (Finset.mem_filter.mp hs).2
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa using (hFrozenRel G π (π.symm w) (π.symm w)).mpr hsF

        have himage_inj : ∀ A B : Finset V, A.image π = B.image π → A = B := by
          intro A B hab
          ext x
          constructor
          · intro hx
            have hπx : π x ∈ B.image π := by
              rw [← hab]
              exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
            rcases Finset.mem_image.mp hπx with ⟨y, hy, hxy⟩
            have : x = y := π.injective hxy.symm
            simpa [this] using hy
          · intro hx
            have hπx : π x ∈ A.image π := by
              rw [hab]
              exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
            rcases Finset.mem_image.mp hπx with ⟨y, hy, hxy⟩
            have : y = x := π.injective hxy
            simpa [this] using hy

        have hclasses : ∀ C : Finset V,
            C ∈ frozenClasses q G ↔ C.image π ∈ frozenClasses q (relabel π G) := by
          intro C
          constructor
          · intro hC
            rcases Finset.mem_filter.mp hC with ⟨hCimage, hCne⟩
            rcases Finset.mem_image.mp hCimage with ⟨a, -, hCeq⟩
            rw [← hCeq, ← hClassRel G π a]
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_image.mpr ⟨π a, Finset.mem_univ _, rfl⟩, ?_⟩
            exact ⟨π a, hselfRel (π a)⟩
          · intro hC
            rcases Finset.mem_filter.mp hC with ⟨hCimage, hCne⟩
            rcases Finset.mem_image.mp hCimage with ⟨w, -, hCeq⟩
            have hpre :
                (frozenClass q G (π.symm w)).image π = C.image π := by
              calc
                (frozenClass q G (π.symm w)).image π =
                    frozenClass q (relabel π G) (π (π.symm w)) :=
                  (hClassRel G π (π.symm w)).symm
                _ = C.image π := by simpa using hCeq
            have hpreMem : frozenClass q G (π.symm w) ∈ frozenClasses q G := by
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_image.mpr ⟨π.symm w, Finset.mem_univ _, rfl⟩, ?_⟩
              exact ⟨π.symm w, hselfG (π.symm w)⟩
            have hpreEq : frozenClass q G (π.symm w) = C :=
              himage_inj _ _ hpre
            rw [← hpreEq]
            exact hpreMem

        let eFin : Finset V ≃ Finset W :=
          { toFun := fun C => C.image π
            invFun := fun D => D.image π.symm
            left_inv := by intro C; ext x; simp
            right_inv := by intro D; ext x; simp }
        have hsum :
            (∑ C ∈ frozenClasses q G,
              ((C.card : ℝ) / (Fintype.card V : ℝ)) ^ 2) =
            ∑ D ∈ frozenClasses q (relabel π G),
              ((D.card : ℝ) / (Fintype.card W : ℝ)) ^ 2 := by
          apply Finset.sum_equiv eFin hclasses
          intro C hC
          change ((C.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 =
            (((C.image π).card : ℝ) / (Fintype.card W : ℝ)) ^ 2
          rw [Finset.card_image_of_injective _ π.injective, Fintype.card_congr π]
        unfold classMass
        exact hsum.symm
      · have hcr : ¬ Colorable q (relabel π G) := by
          intro hr
          exact hc ((hColorRel G π).mp hr)
        have hsrc : frozenClasses q G = ∅ := by
          simp [frozenClasses, frozenClass, Frozen, hc]
        have hdst : frozenClasses q (relabel π G) = ∅ := by
          simp [frozenClasses, frozenClass, Frozen, hcr]
        simp [classMass, hsrc, hdst]
  · intro G
    exact uniformProb_range (FrozenPair q G)

end ThLean.W.S305

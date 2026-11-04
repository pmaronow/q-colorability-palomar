module

public import ThLean.BP.S3.Adapters

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
universe u v

namespace ThLean.W.S388

open ThresholdFoundations

private def sym2Equiv {V : Type u} {W : Type v} (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := by
    intro x
    simp [Sym2.map_map]
  right_inv := by
    intro x
    simp [Sym2.map_map]

private def pairEquiv {V : Type u} {W : Type v} (e : V ≃ W) : Pair V ≃ Pair W where
  toFun p := ⟨Sym2.map e p.val, by
    intro w hw
    obtain ⟨a, rfl⟩ := e.surjective w
    apply p.property a
    exact (Sym2.map.injective e.injective) (by simpa using hw)
  ⟩
  invFun p := ⟨Sym2.map e.symm p.val, by
    intro a ha
    have hp : p.val = s(e a, e a) := by
      have h := congrArg (Sym2.map e) ha
      simpa [Sym2.map_map] using h
    exact p.property (e a) hp
  ⟩
  left_inv := by
    intro p
    apply Subtype.ext
    simp [Sym2.map_map]
  right_inv := by
    intro p
    apply Subtype.ext
    simp [Sym2.map_map]

private def tupleEquiv {V : Type u} {W : Type v} (e : V ≃ W) (m : ℕ) :
    EdgeTuple V m ≃ EdgeTuple W m :=
  Equiv.arrowCongr (Equiv.refl (Fin m)) (pairEquiv e)

private lemma mapGraph_apply_map {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (G : MGraph V) (x : Sym2 V) :
    mapGraph e G (Sym2.map e x) = G x := by
  classical
  unfold mapGraph
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    have hne : Sym2.map e y ≠ Sym2.map e x := by
      intro h
      exact hy (Sym2.map.injective e.injective h)
    simp [hne]
  · simp

private lemma relabel_apply_map {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (G : MGraph V) (x : Sym2 V) :
    relabel e G (Sym2.map e x) = G x := mapGraph_apply_map e G x

private lemma touches_map_iff {V : Type u} {W : Type v} (e : V ≃ W) (a : V)
    (x : Sym2 V) : Touches (e a) (Sym2.map e x) ↔ Touches a x := by
  induction x using Sym2.inductionOn with
  | hf b c =>
      change (∃ w, Sym2.map e (s(b, c)) = s(e a, w)) ↔
        (∃ d, s(b, c) = s(a, d))
      simp only [Sym2.map_mk, Sym2.eq_iff]
      constructor
      · rintro ⟨w, h | h⟩
        · rcases h with ⟨hb, _⟩
          exact ⟨c, Or.inl ⟨e.injective hb, rfl⟩⟩
        · rcases h with ⟨_, hc⟩
          exact ⟨b, Or.inr ⟨rfl, e.injective hc⟩⟩
      · rintro ⟨d, h | h⟩
        · rcases h with ⟨hb, hc⟩
          exact ⟨e d, Or.inl ⟨congrArg e hb, congrArg e hc⟩⟩
        · rcases h with ⟨hb, hc⟩
          exact ⟨e b, Or.inr ⟨rfl, congrArg e hc⟩⟩

private lemma relabel_degree {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (G : MGraph V) (a : V) :
    degree (relabel e G) (e a) = degree G a := by
  classical
  unfold degree
  let E := sym2Equiv e
  calc
    (∑ y : Sym2 W, if Touches (e a) y then relabel e G y else 0)
        = ∑ x : Sym2 V,
            if Touches (e a) (Sym2.map e x) then relabel e G (Sym2.map e x) else 0 := by
          exact (Equiv.sum_comp E (fun y => if Touches (e a) y then relabel e G y else 0)).symm
    _ = ∑ x : Sym2 V, if Touches a x then G x else 0 := by
          apply Fintype.sum_congr
          intro x
          simp [touches_map_iff, relabel_apply_map]

private lemma isColoring_relabel_iff {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (q : ℕ) (G : MGraph V) (σ : V → Fin q) :
    IsColoring q (relabel e G) (σ ∘ e.symm) ↔ IsColoring q G σ := by
  constructor
  · intro h a b hab
    have hEq : relabel e G (s(e a, e b)) = G (s(a, b)) := by
      simpa using relabel_apply_map e G (s(a, b))
    have hpos : 0 < relabel e G (s(e a, e b)) := by
      rw [hEq]
      exact hab
    have h' := h (e a) (e b) hpos
    simpa using h'
  · intro h a b hab
    have hEq : relabel e G (s(a, b)) = G (s(e.symm a, e.symm b)) := by
      simpa using relabel_apply_map e G (s(e.symm a, e.symm b))
    have hpos : 0 < G (s(e.symm a, e.symm b)) := by
      rw [← hEq]
      exact hab
    have h' := h (e.symm a) (e.symm b) hpos
    simpa using h'

private lemma colorable_relabel_iff {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (q : ℕ) (G : MGraph V) :
    Colorable q (relabel e G) ↔ Colorable q G := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ ∘ e, ?_⟩
    have h' : IsColoring q (relabel e G) ((σ ∘ e) ∘ e.symm) := by
      simpa [Function.comp_def] using hσ
    exact (isColoring_relabel_iff e q G (σ ∘ e)).mp h'
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ e.symm, (isColoring_relabel_iff e q G σ).mpr hσ⟩

private lemma frozen_relabel_iff {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (q : ℕ) (G : MGraph V) (a b : V) :
    Frozen q (relabel e G) (e a) (e b) ↔ Frozen q G a b := by
  unfold Frozen
  constructor
  · rintro ⟨hc, hfreeze⟩
    refine ⟨(colorable_relabel_iff e q G).mp hc, ?_⟩
    intro σ hσ
    have hr : IsColoring q (relabel e G) (σ ∘ e.symm) :=
      (isColoring_relabel_iff e q G σ).mpr hσ
    have hv := hfreeze (σ ∘ e.symm) hr
    simpa [Function.comp_def] using hv
  · rintro ⟨hc, hfreeze⟩
    refine ⟨(colorable_relabel_iff e q G).mpr hc, ?_⟩
    intro σ hσ
    have hs : IsColoring q G (σ ∘ e) := by
      apply (isColoring_relabel_iff e q G (σ ∘ e)).mp
      simpa [Function.comp_def] using hσ
    have hv := hfreeze (σ ∘ e) hs
    simpa [Function.comp_def] using hv

private lemma relabel_add {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (G H : MGraph V) :
    relabel e (G + H) = relabel e G + relabel e H := by
  classical
  funext y
  unfold relabel mapGraph
  calc
    (∑ x : Sym2 V, if Sym2.map e x = y then G x + H x else 0)
        = ∑ x : Sym2 V, ((if Sym2.map e x = y then G x else 0) +
            (if Sym2.map e x = y then H x else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : Sym2.map e x = y <;> simp [h]
    _ = (∑ x : Sym2 V, if Sym2.map e x = y then G x else 0) +
          ∑ x : Sym2 V, if Sym2.map e x = y then H x else 0 := by
          rw [Finset.sum_add_distrib]

private lemma tupleGraph_relabel {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) {m : ℕ} (x : EdgeTuple V m) :
    relabel e (tupleGraph x) = tupleGraph (tupleEquiv e m x) := by
  classical
  funext y
  obtain ⟨z, rfl⟩ := (sym2Equiv e).surjective y
  change relabel e (tupleGraph x) (Sym2.map e z) = _
  rw [relabel_apply_map]
  unfold tupleGraph
  congr 1
  ext i
  simp [tupleEquiv, pairEquiv, sym2Equiv, (Sym2.map.injective e.injective).eq_iff]

private lemma uniformMean_reindex {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : uniformMean (f ∘ e) = uniformMean f := by
  unfold uniformMean
  change (∑ a : A, f (e a)) / (Fintype.card A : ℝ) = _
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

private lemma uniformProb_congr {A : Type u} [Fintype A] (P Q : A → Prop)
    (h : ∀ a, P a ↔ Q a) : uniformProb P = uniformProb Q := by
  classical
  unfold uniformProb uniformMean indicator
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp [h a]

private lemma uniformProb_reindex {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) :
    uniformProb (P ∘ e) = uniformProb P := by
  unfold uniformProb
  exact uniformMean_reindex e (fun b => indicator (P b))

private lemma relabel_survival {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (q : ℕ) (G : MGraph V) (k : ℕ) :
    survival q (relabel e G) k = survival q G k := by
  classical
  unfold survival
  rw [← uniformProb_reindex (tupleEquiv e k)]
  apply uniformProb_congr
  intro x
  change Colorable q (relabel e G + tupleGraph (tupleEquiv e k x)) ↔
    Colorable q (G + tupleGraph x)
  rw [← tupleGraph_relabel e x, ← relabel_add e G (tupleGraph x)]
  exact colorable_relabel_iff e q (G + tupleGraph x)

private lemma relabel_lifetime {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (q : ℕ) (G : MGraph V) :
    lifetime q (relabel e G) = lifetime q G := by
  unfold lifetime
  apply tsum_congr
  intro k
  exact congrArg ENNReal.ofReal (relabel_survival e q G k)

private lemma relabel_truncatedLifetime {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] (e : V ≃ W) (q b : ℕ) (G : MGraph V) :
    truncatedLifetime q b (relabel e G) = truncatedLifetime q b G := by
  unfold truncatedLifetime
  apply Finset.sum_congr rfl
  intro k hk
  exact relabel_survival e q G k

private lemma graphMean_relabel {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (m : ℕ) (h : MGraph W → ℝ) :
    graphMean m (fun G : MGraph V => h (relabel e G)) = graphMean m h := by
  unfold graphMean
  calc
    uniformMean (fun x : EdgeTuple V m => h (relabel e (tupleGraph x)))
        = uniformMean (fun x : EdgeTuple V m => h (tupleGraph (tupleEquiv e m x))) := by
          congr 1
          funext x
          rw [tupleGraph_relabel]
    _ = uniformMean (fun y : EdgeTuple W m => h (tupleGraph y)) :=
          uniformMean_reindex (tupleEquiv e m) (fun y => h (tupleGraph y))

theorem S3_01bStatement_holds : ThLean.BP.S3.S3_01bStatement := by
  intro V W instV instW e q G
  constructor
  · exact colorable_relabel_iff e q G
  constructor
  · intro a
    exact relabel_degree e G a
  constructor
  · intro a b
    exact frozen_relabel_iff e q G a b
  constructor
  · exact relabel_lifetime e q G
  constructor
  · intro b
    exact relabel_truncatedLifetime e q b G
  · intro m h
    exact graphMean_relabel e m h

example : ThLean.BP.S3.S3_01bStatement := S3_01bStatement_holds

end ThLean.W.S388

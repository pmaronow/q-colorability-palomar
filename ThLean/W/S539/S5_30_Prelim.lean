module

public import ThLean.BP.S5.Occupation

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S539
open ThresholdFoundations ThLean.BP.S5

variable {V : Type*} [Fintype V]

def sym2Perm (π : Equiv.Perm V) : Sym2 V ≃ Sym2 V where
  toFun := Sym2.map π
  invFun := Sym2.map π.symm
  left_inv z := by
    rw [Sym2.map_map]
    have h : π.symm ∘ π = id := funext π.symm_apply_apply
    rw [h, Sym2.map_id]
    rfl
  right_inv z := by
    rw [Sym2.map_map]
    have h : π ∘ π.symm = id := funext π.apply_symm_apply
    rw [h, Sym2.map_id]
    rfl

lemma mapGraph_equiv_apply (e : V ≃ V) (G : MGraph V) (z : Sym2 V) :
    mapGraph e G z = G (Sym2.map e.symm z) := by
  classical
  unfold mapGraph
  let E := sym2Perm e
  change (∑ x : Sym2 V, if Sym2.map e x = z then G x else 0) = _
  calc
    _ = ∑ y : Sym2 V, if y = z then G (Sym2.map e.symm y) else 0 := by
      apply Fintype.sum_equiv E
      intro x
      change (if Sym2.map e x = z then G x else 0) =
        (if Sym2.map e x = z then G (Sym2.map e.symm (Sym2.map e x)) else 0)
      have hcancel : Sym2.map e.symm (Sym2.map e x) = x := E.left_inv x
      simp [hcancel]
    _ = G (Sym2.map e.symm z) := by simp

lemma pair_card : Fintype.card (Pair V) = (Fintype.card V).choose 2 := by
  classical
  have hp : ∀ z : Sym2 V,
      (∀ v : V, z ≠ s(v, v)) ↔ ¬ z.IsDiag := by
    intro z
    refine Sym2.inductionOn z ?_
    intro a b
    simp only [Sym2.mk_isDiag_iff]
    constructor
    · intro h hab
      subst b
      exact h a rfl
    · intro hab v hv
      rcases Sym2.eq_iff.mp hv with ⟨hav, hbv⟩ | ⟨hav, hbv⟩
      · exact hab (hav.trans hbv.symm)
      · exact hab (hav.trans hbv.symm)
  let E := Equiv.subtypeEquivRight hp
  calc
    Fintype.card (Pair V) = Fintype.card {z : Sym2 V // ¬ z.IsDiag} := Fintype.card_congr E
    _ = (Fintype.card V).choose 2 := Sym2.card_subtype_not_diag

lemma frozen_symm {q : ℕ} {G : MGraph V} {a b : V}
    (h : Frozen q G a b) : Frozen q G b a := by
  rcases h with ⟨hc, h⟩
  exact ⟨hc, fun σ hs => (h σ hs).symm⟩

lemma coloring_relabel_iff (e : V ≃ V) (q : ℕ) (G : MGraph V)
    (σ : V → Fin q) :
    IsColoring q (relabel e G) σ ↔ IsColoring q G (σ ∘ e) := by
  constructor
  · intro h x y hxy
    have heq : relabel e G (s(e x, e y)) = G (s(x, y)) := by
      rw [relabel, mapGraph_equiv_apply]
      simp
    apply h (e x) (e y)
    rw [heq]
    exact hxy
  · intro h x y hxy
    have heq : relabel e G (s(x, y)) = G (s(e.symm x, e.symm y)) := by
      rw [relabel, mapGraph_equiv_apply]
      simp
    have hxy' : 0 < G (s(e.symm x, e.symm y)) := by
      rw [← heq]
      exact hxy
    simpa using h (e.symm x) (e.symm y) hxy'

lemma colorable_relabel_iff (e : V ≃ V) (q : ℕ) (G : MGraph V) :
    Colorable q (relabel e G) ↔ Colorable q G := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ e, (coloring_relabel_iff e q G σ).mp hσ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ ∘ e.symm, ?_⟩
    apply (coloring_relabel_iff e q G (σ ∘ e.symm)).mpr
    simpa [Function.comp_def] using hσ

lemma frozen_relabel_iff (e : V ≃ V) (q : ℕ) (G : MGraph V) (a b : V) :
    Frozen q (relabel e G) (e a) (e b) ↔ Frozen q G a b := by
  constructor
  · rintro ⟨hc, hfreeze⟩
    refine ⟨(colorable_relabel_iff e q G).mp hc, ?_⟩
    intro σ hσ
    have hcolor : IsColoring q (relabel e G) (σ ∘ e.symm) := by
      apply (coloring_relabel_iff e q G (σ ∘ e.symm)).mpr
      simpa [Function.comp_def] using hσ
    simpa [Function.comp_def] using hfreeze (σ ∘ e.symm) hcolor
  · rintro ⟨hc, hfreeze⟩
    refine ⟨(colorable_relabel_iff e q G).mpr hc, ?_⟩
    intro σ hσ
    have hcolor : IsColoring q G (σ ∘ e) :=
      (coloring_relabel_iff e q G σ).mp hσ
    simpa [Function.comp_def] using hfreeze (σ ∘ e) hcolor

lemma degree_relabel (e : V ≃ V) (G : MGraph V) (a : V) :
    degree (relabel e G) (e a) = degree G a := by
  classical
  unfold degree relabel
  change (∑ z : Sym2 V, if Touches (e a) z then mapGraph e G z else 0) = _
  have hs :
      (∑ z : Sym2 V, if Touches (e a) (Sym2.map e z) then G z else 0) =
      (∑ z : Sym2 V, if Touches (e a) z then mapGraph e G z else 0) := by
    apply Fintype.sum_equiv (sym2Perm e)
    intro z
    have hcancel : mapGraph e G (Sym2.map e z) = G z := by
      rw [mapGraph_equiv_apply]
      exact congrArg G ((sym2Perm e).left_inv z)
    change (if Touches (e a) (Sym2.map e z) then G z else 0) =
      (if Touches (e a) (Sym2.map e z) then mapGraph e G (Sym2.map e z) else 0)
    simp [hcancel]
  rw [← hs]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases ht : Touches (e a) (Sym2.map e z)
  · have ht' : Touches a z := by
      rcases ht with ⟨v, hv⟩
      refine ⟨e.symm v, ?_⟩
      apply (Sym2.map.injective e.injective)
      simpa [Sym2.map_mk] using hv
    simp only [if_pos ht, if_pos ht']
  · have ht' : ¬ Touches a z := by
      intro hz'
      rcases hz' with ⟨v, hv⟩
      apply ht
      refine ⟨e v, ?_⟩
      simpa [Sym2.map_mk, hv]
    simp only [if_neg ht, if_neg ht']

def lowRootTerm (q D : ℕ) (f : MGraph V → ℝ) (a : V) (G : MGraph V) : ℝ :=
  indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) * f G

lemma partnerCount_relabel (e : V ≃ V) (q : ℕ) (G : MGraph V) (a : V) :
    partnerCount q (relabel e G) (e a) = partnerCount q G a := by
  classical
  unfold partnerCount frozenPartnerCount
  have hrel (v : V) :
      Frozen q (relabel e G) (e a) v ↔ Frozen q G a (e.symm v) := by
    simpa using frozen_relabel_iff e q G a (e.symm v)
  have hset :
      (Finset.univ.filter (fun v => v ≠ e a ∧ Frozen q (relabel e G) (e a) v)) =
      (Finset.univ.filter (fun v => v ≠ a ∧ Frozen q G a v)).map e.toEmbedding := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨hne, hf⟩
      refine ⟨e.symm v, ⟨?_, ?_⟩, e.apply_symm_apply v⟩
      · intro h
        apply hne
        have hv : v = e a := by simpa using congrArg e h
        exact hv
      · exact (hrel v).mp hf
    · rintro ⟨u, ⟨hne, hf⟩, huv⟩
      subst v
      constructor
      · intro h
        apply hne
        exact e.injective (by simpa using h)
      · exact (hrel (e u)).mpr (by simpa using hf)
  rw [hset, Finset.card_map]

lemma lowRootTerm_relabel (e : V ≃ V) (q D : ℕ) (f : MGraph V → ℝ)
    (hfi : relabelInvariant f) (G : MGraph V) (a : V) :
    lowRootTerm q D f (e a) (relabel e G) = lowRootTerm q D f a G := by
  unfold lowRootTerm
  rw [degree_relabel, partnerCount_relabel, hfi]

def lowIncidences (q D : ℕ) (G : MGraph V) :=
  Σ a : V, {v : V // v ≠ a ∧ Frozen q G a v ∧ degree G a ≤ D}

lemma subtype_card_eq_filter {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] :
    Fintype.card {x : α // P x} = (Finset.univ.filter P).card := by
  let E : {x : α // P x} ≃ Finset.univ.filter P :=
    Equiv.subtypeEquivRight (fun x => by simp)
  calc
    Fintype.card {x : α // P x} = Fintype.card (Finset.univ.filter P) := Fintype.card_congr E
    _ = (Finset.univ.filter P).card := Fintype.card_coe _

lemma frozenPair_repr {q : ℕ} {G : MGraph V} {e : Pair V}
    (h : FrozenPair q G e) {a b : V} (hab : e.val = s(a, b)) : Frozen q G a b := by
  rcases h with ⟨x, y, hxy, hf⟩
  have hEq : s(x, y) = s(a, b) := hxy.symm.trans hab
  rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hf
  · exact frozen_symm hf

lemma lowPair_card_le_incidence_card (q D : ℕ) (G : MGraph V)
    [Fintype (lowIncidences q D G)] :
    Fintype.card {e : Pair V // FrozenPair q G e ∧ lowEdge G D e} ≤
      Fintype.card (lowIncidences q D G) := by
  classical
  let A := {e : Pair V // FrozenPair q G e ∧ lowEdge G D e}
  let B := lowIncidences q D G
  let lowVertex (x : A) : V := Classical.choose x.2.2
  have hlowVertex (x : A) : Touches (lowVertex x) x.1.val ∧ degree G (lowVertex x) ≤ D :=
    Classical.choose_spec x.2.2
  let partner (x : A) : V := Classical.choose (hlowVertex x).1
  have hpartner (x : A) : x.1.val = s(lowVertex x, partner x) :=
    Classical.choose_spec (hlowVertex x).1
  let φ (x : A) : B :=
    ⟨lowVertex x, ⟨partner x, by
      refine ⟨?_, frozenPair_repr x.2.1 (hpartner x), (hlowVertex x).2⟩
      intro h
      apply x.1.property (lowVertex x)
      rw [hpartner x, h]
  ⟩⟩
  refine Fintype.card_le_of_injective φ ?_
  intro x y hxy
  have ha : lowVertex x = lowVertex y := congrArg Sigma.fst hxy
  have hb : partner x = partner y := congrArg (fun z : B => z.2.val) hxy
  apply Subtype.ext
  apply Subtype.ext
  rw [hpartner x, hpartner y, ha, hb]

lemma lowIncidence_card (q D : ℕ) (G : MGraph V)
    [Fintype (lowIncidences q D G)] :
    (Fintype.card (lowIncidences q D G) : ℝ) =
      ∑ a : V, indicator (degree G a ≤ D) * (partnerCount q G a : ℝ) := by
  classical
  letI : Fintype (Σ a : V, {v : V // v ≠ a ∧ Frozen q G a v ∧ degree G a ≤ D}) := inferInstance
  have hcard : Fintype.card (lowIncidences q D G) =
      Fintype.card (Σ a : V, {v : V // v ≠ a ∧ Frozen q G a v ∧ degree G a ≤ D}) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hcard, Fintype.card_sigma, Nat.cast_sum]
  have hcard (a : V) :
      Fintype.card {v : V // v ≠ a ∧ Frozen q G a v ∧ degree G a ≤ D} =
        if degree G a ≤ D then partnerCount q G a else 0 := by
    by_cases h : degree G a ≤ D
    · rw [if_pos h]
      let E : {v : V // v ≠ a ∧ Frozen q G a v ∧ degree G a ≤ D} ≃
          {v : V // v ≠ a ∧ Frozen q G a v} :=
        Equiv.subtypeEquivRight (fun v => by simp [h])
      calc
        Fintype.card {v : V // v ≠ a ∧ Frozen q G a v ∧ degree G a ≤ D} =
            Fintype.card {v : V // v ≠ a ∧ Frozen q G a v} := Fintype.card_congr E
        _ = partnerCount q G a := by
            unfold partnerCount frozenPartnerCount
            exact subtype_card_eq_filter (fun v : V => v ≠ a ∧ Frozen q G a v)
    · rw [if_neg h]
      have hempty : IsEmpty {v : V // v ≠ a ∧ Frozen q G a v ∧ degree G a ≤ D} :=
        ⟨fun v => h v.2.2.2⟩
      have hc : Fintype.card {v : V // v ≠ a ∧ Frozen q G a v ∧ degree G a ≤ D} = 0 :=
        Fintype.card_of_isEmpty
      rw [hc]
  simp_rw [hcard]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : degree G a ≤ D <;> simp [indicator, h]

lemma lowPair_card (q D : ℕ) (G : MGraph V) :
    (Fintype.card {e : Pair V // FrozenPair q G e ∧ lowEdge G D e} : ℝ) =
      ∑ e : Pair V, indicator (FrozenPair q G e ∧ lowEdge G D e) := by
  classical
  have hNat :
      Fintype.card {e : Pair V // FrozenPair q G e ∧ lowEdge G D e} =
        ∑ e : Pair V, if FrozenPair q G e ∧ lowEdge G D e then 1 else 0 := by
    rw [subtype_card_eq_filter (fun e : Pair V => FrozenPair q G e ∧ lowEdge G D e),
      Finset.card_filter]
  unfold indicator
  exact_mod_cast hNat

lemma pmf_weight_summable {α : Type*} (ν : PMF α) :
    Summable (fun x => (ν x).toReal) :=
  ENNReal.summable_toReal ν.tsum_coe_ne_top

lemma lawMean_summable_of_bounded {ν : PMF (MGraph V)} {g : MGraph V → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ G, 0 ≤ g G ∧ g G ≤ C) :
    Summable (fun G => (ν G).toReal * g G) := by
  have hw := (pmf_weight_summable ν).mul_left C
  apply Summable.of_nonneg_of_le
  · intro G
    exact mul_nonneg ENNReal.toReal_nonneg (hg G).1
  · intro G
    calc
      (ν G).toReal * g G ≤ (ν G).toReal * C :=
        mul_le_mul_of_nonneg_left (hg G).2 ENNReal.toReal_nonneg
      _ = C * (ν G).toReal := by ring
  · exact hw

def graphPerm (π : Equiv.Perm V) : MGraph V ≃ MGraph V where
  toFun := relabel π
  invFun := relabel π.symm
  left_inv G := by
    funext z
    change mapGraph π.symm (mapGraph π G) z = G z
    rw [mapGraph_equiv_apply, mapGraph_equiv_apply]
    exact congrArg G ((sym2Perm π).left_inv z)
  right_inv G := by
    funext z
    change mapGraph π (mapGraph π.symm G) z = G z
    rw [mapGraph_equiv_apply, mapGraph_equiv_apply]
    exact congrArg G ((sym2Perm π).right_inv z)

lemma pmf_relabel_apply {ν : PMF (MGraph V)} (π : Equiv.Perm V)
    (hν : ν.map (relabel π) = ν) (G : MGraph V) :
    ν (relabel π G) = ν G := by
  classical
  letI : DecidablePred (fun H : MGraph V => relabel π G = relabel π H) := Classical.decPred _
  have h := congrArg (fun μ : PMF (MGraph V) => μ (relabel π G)) hν
  rw [PMF.map_apply] at h
  let f : MGraph V → ℝ≥0∞ := fun H =>
    if relabel π G = relabel π H then ν H else 0
  have h' : (∑' H, f H) = ν (relabel π G) := by
    simpa [f] using h
  have hs : (∑' H, f H) = f G := by
    apply tsum_eq_single G
    intro H hHG
    have hne : relabel π G ≠ relabel π H := by
      intro heq
      exact hHG ((graphPerm π).injective heq).symm
    simp [f, hne]
  calc
    ν (relabel π G) = ∑' H, f H := h'.symm
    _ = f G := hs
    _ = ν G := by simp [f]

lemma lawMean_relabel {ν : PMF (MGraph V)} (π : Equiv.Perm V)
    (hν : ν.map (relabel π) = ν) (g : MGraph V → ℝ) :
    lawMean ν g = lawMean ν (fun G => g (relabel π G)) := by
  have hm (G : MGraph V) := pmf_relabel_apply π hν G
  unfold lawMean
  calc
    (∑' G, (ν G).toReal * g G) =
        ∑' G, (ν (relabel π G)).toReal * g (relabel π G) := by
          exact (graphPerm π).tsum_eq _ |>.symm
    _ = ∑' G, (ν G).toReal * g (relabel π G) := by
          apply tsum_congr
          intro G
          rw [hm G]

end ThLean.W.S539

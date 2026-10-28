import ThLean.Contrib.S554.PartnerAverage

noncomputable section

namespace ThLean.W.S554

open ThresholdFoundations ThLean.BP.S5 ThLean.Contrib.S554
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v

private def sym2Equiv {V : Type u} {W : Type v} (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := by intro z; simp [Sym2.map_map]
  right_inv := by intro z; simp [Sym2.map_map]

private theorem relabel_apply {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (G : MGraph V) (z : Sym2 W) :
    relabel e G z = G (Sym2.map e.symm z) := by
  classical
  let E := sym2Equiv e
  change (∑ x : Sym2 V, if Sym2.map e x = z then G x else 0) = _
  calc
    (∑ x : Sym2 V, if Sym2.map e x = z then G x else 0) =
        ∑ x : Sym2 V, (if E x = z then G (E.symm (E x)) else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [E, sym2Equiv, Sym2.map_map]
    _ = ∑ y : Sym2 W, (if y = z then G (E.symm y) else 0) := by
          let g : Sym2 W → ℕ := fun y => if y = z then G (E.symm y) else 0
          change (∑ x : Sym2 V, g (E x)) = ∑ y : Sym2 W, g y
          exact E.sum_comp g
    _ = G (Sym2.map e.symm z) := by simp [E, sym2Equiv]

private theorem isColoring_relabel_iff {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] (e : V ≃ W) (q : ℕ) (G : MGraph V)
    (σ : W → Fin q) :
    IsColoring q (relabel e G) σ ↔ IsColoring q G (σ ∘ e) := by
  constructor
  · intro h x y hedge
    have hedge' : 0 < relabel e G (s(e x, e y)) := by
      simpa [relabel_apply] using hedge
    simpa using h (e x) (e y) hedge'
  · intro h x y hedge
    have hedge' : 0 < G (s(e.symm x, e.symm y)) := by
      have heq : relabel e G (s(x, y)) = G (s(e.symm x, e.symm y)) := by
        simp [relabel_apply]
      rw [← heq]
      exact hedge
    simpa using h (e.symm x) (e.symm y) hedge'

private theorem colorable_relabel_iff {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] (e : V ≃ W) (q : ℕ) (G : MGraph V) :
    Colorable q (relabel e G) ↔ Colorable q G := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ e, (isColoring_relabel_iff e q G σ).mp hσ⟩
  · rintro ⟨τ, hτ⟩
    let σ : W → Fin q := τ ∘ e.symm
    refine ⟨σ, (isColoring_relabel_iff e q G σ).mpr ?_⟩
    simpa [σ, Function.comp_def] using hτ

private theorem frozen_relabel_iff {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] (e : V ≃ W) (q : ℕ) (G : MGraph V) (a b : V) :
    Frozen q (relabel e G) (e a) (e b) ↔ Frozen q G a b := by
  constructor
  · rintro ⟨hc, hf⟩
    refine ⟨(colorable_relabel_iff e q G).mp hc, ?_⟩
    intro σ hσ
    let τ : W → Fin q := σ ∘ e.symm
    have hτ : IsColoring q (relabel e G) τ := by
      apply (isColoring_relabel_iff e q G τ).mpr
      simpa [τ, Function.comp_def] using hσ
    have heq := hf τ hτ
    simpa [τ, Function.comp_def] using heq
  · rintro ⟨hc, hf⟩
    refine ⟨(colorable_relabel_iff e q G).mpr hc, ?_⟩
    intro σ hσ
    have hσ' : IsColoring q G (σ ∘ e) :=
      (isColoring_relabel_iff e q G σ).mp hσ
    have heq := hf (σ ∘ e) hσ'
    simpa using heq

private def graphRelabelEquiv {V : Type u} [Fintype V] (e : Equiv.Perm V) :
    MGraph V ≃ MGraph V where
  toFun := relabel e
  invFun := relabel e.symm
  left_inv := by
    intro G
    funext z
    rw [relabel_apply, relabel_apply]
    simp [Sym2.map_map]
  right_inv := by
    intro G
    funext z
    rw [relabel_apply, relabel_apply]
    simp [Sym2.map_map]

private theorem partnerCount_relabel
    {V : Type} [Fintype V]
    (e : Equiv.Perm V) (q : ℕ) (G : MGraph V) (a : V) :
    partnerCount q (relabel e G) (e a) = partnerCount q G a := by
  classical
  have hFrozen : ∀ b, Frozen q (relabel e G) (e a) (e b) ↔ Frozen q G a b :=
    fun b => frozen_relabel_iff e q G a b
  let E : {b : V // b ≠ a ∧ Frozen q G a b} ≃
      {b : V // b ≠ e a ∧ Frozen q (relabel e G) (e a) b} := {
    toFun b := ⟨e b.1, by
      constructor
      · intro he
        exact b.2.1 (e.injective he)
      · exact (hFrozen b.1).mpr b.2.2⟩
    invFun b := ⟨e.symm b.1, by
      constructor
      · intro he
        apply b.2.1
        calc
          b.1 = e (e.symm b.1) := (e.apply_symm_apply _).symm
          _ = e a := congrArg e he
      · exact (hFrozen (e.symm b.1)).mp (by simpa using b.2.2)⟩
    left_inv := by intro b; apply Subtype.ext; simp
    right_inv := by intro b; apply Subtype.ext; simp }
  simpa [partnerCount, frozenPartnerCount, Fintype.card_subtype] using
    (Fintype.card_congr E).symm

private theorem invariantRootMean_of_relabel
    : InvariantRootMeanStatement := by
  classical
  intro V hV q ν hν a b
  let e : Equiv.Perm V := Equiv.swap a b
  let f : MGraph V ≃ MGraph V := graphRelabelEquiv e
  have hMass : ∀ G : MGraph V, (ν (relabel e G)).toReal = (ν G).toReal := by
    intro G
    have hmap := congrArg (fun p : PMF (MGraph V) => p (relabel e G)) (hν e)
    rw [PMF.map_apply] at hmap
    have hsingle :
        (∑' H : MGraph V, @ite ENNReal (relabel e G = relabel e H)
          (Classical.propDecidable _) (ν H) 0) = ν G := by
      rw [tsum_eq_single G]
      · simp
      · intro H hHG
        have hne : relabel e G ≠ relabel e H := fun heq => by
          apply hHG
          exact f.injective (by simpa [f, graphRelabelEquiv] using heq.symm)
        simp [hne]
    have hprob : ν G = ν (relabel e G) := hsingle.symm.trans hmap
    exact congrArg ENNReal.toReal hprob.symm
  have hsum :
      lawMean ν (fun G => (partnerCount q G (e a) : ℝ)) =
        lawMean ν (fun G => (partnerCount q G a : ℝ)) := by
    unfold lawMean
    calc
      (∑' G, (ν G).toReal * (partnerCount q G (e a) : ℝ)) =
          ∑' G, (ν (relabel e G)).toReal *
            (partnerCount q (relabel e G) (e a) : ℝ) :=
              (f.tsum_eq (fun G => (ν G).toReal *
                (partnerCount q G (e a) : ℝ))).symm
      _ = ∑' G, (ν G).toReal * (partnerCount q G a : ℝ) := by
            apply tsum_congr
            intro G
            rw [partnerCount_relabel e q G a, hMass]
  simpa [e] using hsum.symm

private abbrev OrientFrozen (V : Type) [Fintype V] (q : ℕ) (G : MGraph V) :=
  {p : V × V // p.1 ≠ p.2 ∧ Frozen q G p.1 p.2}

private theorem frozen_symm {V : Type} [Fintype V] (q : ℕ) (G : MGraph V)
    {a b : V} (h : Frozen q G a b) : Frozen q G b a := by
  rcases h with ⟨hc, hf⟩
  refine ⟨hc, ?_⟩
  intro σ hs
  exact (hf σ hs).symm

private def orientToPair {V : Type} [Fintype V] (q : ℕ) (G : MGraph V) :
    OrientFrozen V q G → Pair V := fun p =>
  ⟨s(p.1.1, p.1.2), by
    intro x hx
    have hEq : s(p.1.1, p.1.2) = s(x, x) := hx
    have hSame : p.1.1 = p.1.2 := by
      rcases Sym2.eq_iff.mp hEq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact h₁.trans h₂.symm
      · exact h₁.trans h₂.symm
    exact p.2.1 hSame⟩

private theorem partnerDoubleCount_proved : PartnerDoubleCountStatement := by
  classical
  intro V hV q hVcard G
  let O := OrientFrozen V q G
  let f := orientToPair q G
  let P : Finset (Pair V) := Finset.univ.filter (FrozenPair q G)
  have hImage : Finset.univ.image f = P := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_image.mp he with ⟨p, -, rfl⟩
      have hfp : FrozenPair q G (f p) := ⟨p.1.1, p.1.2, rfl, p.2.2⟩
      simpa [P] using hfp
    · intro he
      have he' : FrozenPair q G e := by simpa [P] using he
      rcases he' with ⟨a, b, hEdge, hFrozen⟩
      have hne : a ≠ b := by
        intro hab
        subst b
        apply e.property a
        exact hEdge
      let p : O := ⟨(a, b), ⟨hne, hFrozen⟩⟩
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      exact hEdge.symm
  have hFiber : ∀ e ∈ Finset.univ.image f,
      (Finset.univ.filter (fun p : O => f p = e)).card = 2 := by
    intro e he
    have heP : FrozenPair q G e := by
      have hmem : e ∈ P := hImage ▸ he
      simpa [P] using hmem
    rcases heP with ⟨a, b, hEdge, hFrozen⟩
    have hne : a ≠ b := by
      intro hab
      subst b
      apply e.property a
      exact hEdge
    let pab : O := ⟨(a, b), ⟨hne, hFrozen⟩⟩
    let pba : O := ⟨(b, a), ⟨hne.symm, frozen_symm q G hFrozen⟩⟩
    have hf₁ : f pab = e := by
      apply Subtype.ext
      exact hEdge.symm
    have hf₂ : f pba = e := by
      apply Subtype.ext
      calc
        s(b, a) = s(a, b) := Sym2.eq_swap
        _ = e.val := hEdge.symm
    have hset : Finset.univ.filter (fun p : O => f p = e) = {pab, pba} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hp
        have hp' : s(p.1.1, p.1.2) = s(a, b) := by
          have hval := congrArg Subtype.val hp
          exact hval.trans hEdge
        rcases Sym2.eq_iff.mp hp' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · left
          apply Subtype.ext
          exact Prod.ext h₁ h₂
        · right
          apply Subtype.ext
          exact Prod.ext h₁ h₂
      · intro hp
        rcases hp with hp | hp
        · exact (congrArg f hp).trans hf₁
        · exact (congrArg f hp).trans hf₂
    rw [hset]
    have hpab : pab ≠ pba := by
      intro hh
      have := congrArg Subtype.val hh
      exact hne (congrArg Prod.fst this)
    simp [hpab]
  have hCardO : Fintype.card O = 2 * P.card := by
    have h₀ : Fintype.card O = (Finset.univ : Finset O).card := by simp
    calc
      Fintype.card O =
          ∑ e ∈ Finset.univ.image f, (Finset.univ.filter (fun p : O => f p = e)).card := by
        rw [h₀, Finset.card_eq_sum_card_image f Finset.univ]
      _ = ∑ e ∈ P, (Finset.univ.filter (fun p : O => f p = e)).card := by rw [hImage]
      _ =
          ∑ e ∈ P, (2 : ℕ) := by
            apply Finset.sum_congr rfl
            intro e he
            exact hFiber e (hImage.symm ▸ he)
      _ = 2 * P.card := by simp [mul_comm]
  have hSigma : Fintype.card O = ∑ a : V, partnerCount q G a := by
    let E : O ≃ Σ a : V, {b : V // b ≠ a ∧ Frozen q G a b} := {
      toFun p := ⟨p.1.1, ⟨p.1.2, p.2.1.symm, p.2.2⟩⟩
      invFun p := ⟨(p.1, p.2.1), p.2.2.1.symm, p.2.2.2⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by
        intro p
        cases p with
        | mk a b => cases b; rfl }
    calc
      Fintype.card O = Fintype.card (Σ a : V, {b : V // b ≠ a ∧ Frozen q G a b}) :=
        Fintype.card_congr E
      _ = ∑ a : V, Fintype.card {b : V // b ≠ a ∧ Frozen q G a b} := Fintype.card_sigma
      _ = ∑ a : V, partnerCount q G a := by
        simp [partnerCount, frozenPartnerCount, Fintype.card_subtype]
  have hPairCard : Fintype.card (Pair V) = (Fintype.card V).choose 2 := by
    let noLoop := fun (z : Sym2 V) => ∀ v : V, z ≠ s(v, v)
    have hdiag : ∀ z : Sym2 V, noLoop z ↔ ¬ z.IsDiag := by
      intro z
      induction z using Sym2.ind with
      | h a b => simp [noLoop, eq_comm]
    let E : Pair V ≃ {z : Sym2 V // ¬ z.IsDiag} := {
      toFun p := ⟨p.val, (hdiag p.val).mp p.property⟩
      invFun p := ⟨p.val, (hdiag p.val).mpr p.property⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro p; cases p; rfl }
    calc
      Fintype.card (Pair V) = Fintype.card {z : Sym2 V // ¬ z.IsDiag} := Fintype.card_congr E
      _ = (Fintype.card V).choose 2 := Sym2.card_subtype_not_diag
  have hpairProd :
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) =
        2 * (Fintype.card (Pair V) : ℝ) := by
    have hdiv : 2 ∣ Fintype.card V * (Fintype.card V - 1) := by
      rcases Nat.even_or_odd (Fintype.card V) with he | ho
      · exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp he) _
      · rcases ho with ⟨k, hk⟩
        have he : Even (Fintype.card V - 1) := ⟨k, by omega⟩
        exact dvd_mul_of_dvd_right (even_iff_two_dvd.mp he) _
    have hn : Fintype.card V * (Fintype.card V - 1) = 2 * (Fintype.card V).choose 2 := by
      rw [Nat.choose_two_right]
      exact (Nat.mul_div_cancel' hdiv).symm
    rw [hPairCard]
    have hcast : ((Fintype.card V - 1 : ℕ) : ℝ) =
        (Fintype.card V : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
      norm_num
    rw [← hcast]
    exact_mod_cast hn
  have hkappa : kappa q G = (P.card : ℝ) / (Fintype.card (Pair V) : ℝ) := by
    unfold kappa uniformProb uniformMean
    change (∑ e : Pair V, if FrozenPair q G e then (1 : ℝ) else 0) /
      (Fintype.card (Pair V) : ℝ) = (P.card : ℝ) / _
    have hsum :
        (∑ e : Pair V, if FrozenPair q G e then (1 : ℝ) else 0) = (P.card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [P]
    rw [hsum]
  have hdoubleNat : (∑ a : V, partnerCount q G a) = 2 * P.card := by
    exact hSigma.symm.trans hCardO
  have hdoubleReal :
      (∑ a : V, (partnerCount q G a : ℝ)) = 2 * (P.card : ℝ) := by
    exact_mod_cast hdoubleNat
  have hpairPos : 0 < (Fintype.card (Pair V) : ℝ) := by
    have hcard : 0 < Fintype.card (Pair V) := by
      rw [hPairCard]
      exact Nat.choose_pos (by omega)
    exact_mod_cast hcard
  rw [hkappa]
  calc
    (∑ a : V, (partnerCount q G a : ℝ)) = 2 * (P.card : ℝ) := hdoubleReal
    _ = (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) *
        ((P.card : ℝ) / (Fintype.card (Pair V) : ℝ)) := by
      rw [hpairProd]
      field_simp [ne_of_gt hpairPos]

theorem S5_12Statement_of_helpers
    (hDouble : PartnerDoubleCountStatement) :
    ThLean.BP.S5.S5_12Statement := by
  classical
  intro V hVtype q hq hV ν hν a
  have hRoot : InvariantRootMeanStatement := invariantRootMean_of_relabel
  let μ : MGraph V → ℝ := fun G => (ν G).toReal
  have hμ : Summable μ := ENNReal.summable_toReal ν.tsum_coe_ne_top
  have hμnonneg : ∀ G, 0 ≤ μ G := fun G => ENNReal.toReal_nonneg
  have hpcNat : ∀ G (b : V), partnerCount q G b ≤ Fintype.card V := by
    intro G b
    simp only [partnerCount, frozenPartnerCount]
    exact Finset.card_filter_le _ _
  have hpcSummable : ∀ b : V,
      Summable (fun G => μ G * (partnerCount q G b : ℝ)) := by
    intro b
    apply (hμ.mul_left (Fintype.card V : ℝ)).of_norm_bounded
    intro G
    rw [Real.norm_of_nonneg (mul_nonneg (hμnonneg G) (by positivity))]
    calc
      μ G * (partnerCount q G b : ℝ) = (partnerCount q G b : ℝ) * μ G := by ring
      _ ≤ (Fintype.card V : ℝ) * μ G :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hpcNat G b) (hμnonneg G)
  have hκnonneg : ∀ G : MGraph V, 0 ≤ kappa q G := by
    intro G
    unfold kappa uniformProb uniformMean indicator
    apply div_nonneg
    · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    · positivity
  have hκle : ∀ G : MGraph V, kappa q G ≤ 1 := by
    intro G
    have hpairs : 0 < Fintype.card (Pair V) := by
      have hc : Fintype.card (Pair V) = (Fintype.card V).choose 2 := by
        let noLoop := fun (z : Sym2 V) => (∀ v : V, z ≠ s(v, v))
        have hdiag : ∀ z : Sym2 V, noLoop z ↔ ¬ z.IsDiag := by
          intro z
          induction z using Sym2.ind with
          | h x y => simp [noLoop, eq_comm]
        let e : Pair V ≃ {z : Sym2 V // ¬ z.IsDiag} := {
          toFun := fun p => ⟨p.val, (hdiag p.val).mp p.property⟩
          invFun := fun p => ⟨p.val, (hdiag p.val).mpr p.property⟩
          left_inv := by intro p; cases p; rfl
          right_inv := by intro p; cases p; rfl }
        calc
          Fintype.card (Pair V) = Fintype.card {z : Sym2 V // ¬ z.IsDiag} := Fintype.card_congr e
          _ = (Fintype.card V).choose 2 := Sym2.card_subtype_not_diag
      rw [hc]
      exact Nat.choose_pos (by omega)
    have hnum : (∑ e : Pair V, indicator (FrozenPair q G e) : ℝ) ≤ Fintype.card (Pair V) := by
      calc
        (∑ e : Pair V, indicator (FrozenPair q G e) : ℝ) ≤ ∑ _e : Pair V, (1 : ℝ) :=
          Finset.sum_le_sum fun e _ => by simp [indicator]; split_ifs <;> norm_num
        _ = Fintype.card (Pair V) := by simp
    unfold kappa uniformProb uniformMean indicator
    dsimp
    rw [div_le_iff₀ (by exact_mod_cast hpairs)]
    simpa [indicator] using hnum
  have hκSummable : Summable (fun G => μ G * kappa q G) := by
    apply hμ.of_norm_bounded
    intro G
    rw [Real.norm_of_nonneg (mul_nonneg (hμnonneg G) (hκnonneg G))]
    calc
      μ G * kappa q G ≤ μ G * 1 := mul_le_mul_of_nonneg_left (hκle G) (hμnonneg G)
      _ = μ G := by ring
  have hsumMean :
      (∑ b : V, lawMean ν (fun G => (partnerCount q G b : ℝ))) =
        lawMean ν (fun G => ∑ b : V, (partnerCount q G b : ℝ)) := by
    change (∑ b : V, ∑' G, μ G * (partnerCount q G b : ℝ)) =
      ∑' G, μ G * (∑ b : V, (partnerCount q G b : ℝ))
    symm
    rw [← Summable.tsum_finsetSum (s := Finset.univ) (fun b _ => hpcSummable b)]
    congr 1
    funext G
    rw [Finset.mul_sum]
  have htotal : lawMean ν (fun G => ∑ b : V, (partnerCount q G b : ℝ)) =
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) * lawMean ν (kappa q) := by
    change (∑' G, μ G * (∑ b : V, (partnerCount q G b : ℝ))) =
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) * (∑' G, μ G * kappa q G)
    calc
      (∑' G, μ G * (∑ b : V, (partnerCount q G b : ℝ))) =
          ∑' G, ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) * (μ G * kappa q G) := by
        apply tsum_congr
        intro G
        rw [hDouble V q hV G]
        ring
      _ = (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) *
          (∑' G, μ G * kappa q G) := by rw [tsum_mul_left]
  have hrootEq : ∀ b : V,
      lawMean ν (fun G => (partnerCount q G b : ℝ)) =
        lawMean ν (fun G => (partnerCount q G a : ℝ)) := by
    intro b
    exact (hRoot V q ν hν b a).trans rfl
  have hmeanSum :
      (Fintype.card V : ℝ) * lawMean ν (fun G => (partnerCount q G a : ℝ)) =
        lawMean ν (fun G => ∑ b : V, (partnerCount q G b : ℝ)) := by
    rw [← hsumMean]
    simp_rw [hrootEq]
    simp
  have hsize : (Fintype.card V : ℝ) ≠ 0 := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast (ne_of_gt this)
  have hcard1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by
    have : 2 ≤ Fintype.card V := hV
    have : (1 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 1 < Fintype.card V)
    linarith
  refine ⟨hpcSummable a, hκSummable, ?_⟩
  have hmean := hmeanSum.trans htotal
  have hmean2 : (Fintype.card V : ℝ) * lawMean ν (fun G => (partnerCount q G a : ℝ)) =
      (Fintype.card V : ℝ) * (((Fintype.card V : ℝ) - 1) * lawMean ν (kappa q)) := by
    calc
      _ = (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) * lawMean ν (kappa q) := hmean
      _ = _ := by ring
  have hmean' : lawMean ν (fun G => (partnerCount q G a : ℝ)) =
      ((Fintype.card V : ℝ) - 1) * lawMean ν (kappa q) :=
    mul_left_cancel₀ hsize hmean2
  rw [hmean']
  exact mul_div_cancel_left₀ (lawMean ν (kappa q)) hcard1

theorem S5_12Statement_holds : ThLean.BP.S5.S5_12Statement :=
  S5_12Statement_of_helpers partnerDoubleCount_proved

example : ThLean.BP.S5.S5_12Statement := S5_12Statement_holds

end ThLean.W.S554

import ThLean.W.S541S.Probability
import ThLean.W.S560.S5_01A

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S541S
open ThresholdFoundations ThLean.BP.S5

theorem degree_add {V : Type*} [Fintype V] (G H : MGraph V) (a : V) :
    degree (G + H) a = degree G a + degree H a := by
  simp only [degree, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp

theorem degree_map_some {V : Type*} [Fintype V] (B : MGraph V) :
    degree (mapGraph some B) none = 0 := by
  classical
  unfold degree
  apply Finset.sum_eq_zero
  intro e he
  split_ifs with h
  · obtain ⟨v, rfl⟩ := h
    unfold mapGraph
    apply Finset.sum_eq_zero
    intro p hp
    induction p using Sym2.ind with
    | h u w => cases v <;> simp [Sym2.eq]
  · rfl

theorem degree_star {V : Type*} [Fintype V] (xs : List V) :
    degree (ThresholdFoundations.star xs) none = xs.length := by
  classical
  induction xs with
  | nil => simp [ThresholdFoundations.star, degree]
  | cons v xs ih =>
    have hstar : ThresholdFoundations.star (v :: xs) =
        ThresholdFoundations.star xs +
          (fun e => if e = s(none, some v) then 1 else 0) := by
      funext e
      simp only [ThresholdFoundations.star, List.map_cons, List.count_cons, Pi.add_apply,
        beq_iff_eq]
      split_ifs <;> simp_all
    rw [hstar, degree_add, ih]
    have hone : degree (fun e : Sym2 (Option V) =>
        if e = s(none, some v) then 1 else 0) none = 1 := by
      unfold degree
      have hp (e : Sym2 (Option V)) :
          (if Touches none e then if e = s(none, some v) then 1 else 0 else 0) =
            (if e = s(none, some v) then 1 else 0 : ℕ) := by
        by_cases h : e = s(none, some v)
        · subst e; simp [Touches]
        · simp [h]
      simp_rw [hp]
      simp
    simp [hone]

theorem degree_addRoot {V : Type*} [Fintype V] (B : MGraph V) (xs : List V) :
    degree (addRoot B xs) none = xs.length := by
  rw [addRoot, degree_add, degree_map_some, degree_star, Nat.zero_add]

theorem partnerCount_pos_iff {V : Type*} [Fintype V] (q : ℕ)
    (G : MGraph V) (a : V) :
    0 < partnerCount q G a ↔ ∃ b, b ≠ a ∧ Frozen q G a b := by
  simp only [partnerCount, frozenPartnerCount, Finset.card_pos, Finset.nonempty_def,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- Two available colors for the new root contradict a nontrivial frozen partner. -/
theorem addRoot_frozen_obstruction {V : Type} [Fintype V] (q : ℕ) (hq : 3 ≤ q)
    (B : MGraph V) (xs : List V)
    (hroot : 0 < partnerCount q (addRoot B xs) none) :
    neverMonochromatic q B xs := by
  obtain ⟨b, hb, hfr⟩ := (partnerCount_pos_iff q _ none).1 hroot
  cases b with
  | none => exact (hb rfl).elim
  | some b =>
    have hA := ThLean.W.S560.S5_01AStatement_holds V q hq B xs
    obtain ⟨τ, hτ⟩ := hfr.1
    refine ⟨⟨fun v => τ (some v), ((hA τ).1 hτ).1⟩, ?_⟩
    intro σ hσ
    by_contra hcard
    let C := (xs.map σ).toFinset
    have hsmall : C.card ≤ 1 := by dsimp [C]; omega
    have hfree : 2 ≤ (Finset.univ \ C).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ C)]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp (by omega :
      1 < (Finset.univ \ C).card)
    have hc' : c ∉ C := (Finset.mem_sdiff.mp hc).2
    have hd' : d ∉ C := (Finset.mem_sdiff.mp hd).2
    have hext (k : Fin q) (hk : k ∉ C) :
        IsColoring q (addRoot B xs) (fun v => v.elim k σ) := by
      apply (hA _).2
      refine ⟨hσ, ?_⟩
      intro v hv heq
      apply hk
      change k ∈ (xs.map σ).toFinset
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨v, hv, heq.symm⟩)
    have hcb : c = σ b := hfr.2 _ (hext c hc')
    have hdb : d = σ b := hfr.2 _ (hext d hd')
    exact hcd (hcb.trans hdb.symm)

theorem rootEvent_addRoot_imp {V : Type} [Fintype V] (q D : ℕ) (hq : 3 ≤ q)
    (B : MGraph V) (xs : List V) :
    rootEvent q D none (addRoot B xs) →
      xs.length ≤ D ∧ neverMonochromatic q B xs := by
  intro h
  exact ⟨by simpa [degree_addRoot] using h.1,
    addRoot_frozen_obstruction q hq B xs h.2⟩

theorem rootEvent_relabel (hRelabel : PreRelabelStatement.{0, 0})
    {V W : Type} [Fintype V] [Fintype W] (e : V ≃ W) (q D : ℕ)
    (G : MGraph V) (a : V) :
    rootEvent q D (e a) (relabel e G) ↔ rootEvent q D a G := by
  rw [rootEvent, rootEvent, (hRelabel V W e q G).2.1 a,
    partnerCount_pos_iff, partnerCount_pos_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨b, hb, hfr⟩
    refine ⟨e.symm b, ?_, ?_⟩
    · simpa only [ne_eq, Equiv.symm_apply_eq] using hb
    · apply ((hRelabel V W e q G).2.2.1 a (e.symm b)).1
      simpa using hfr
  · rintro ⟨b, hb, hfr⟩
    exact ⟨e b, fun h => hb (e.injective h),
      ((hRelabel V W e q G).2.2.1 a b).2 hfr⟩

theorem poissonGraphMean_relabel (hRelabel : PreRelabelStatement.{0, 0})
    {V W : Type} [Fintype V] [Fintype W] (e : V ≃ W) (q : ℕ)
    (t : ℝ) (f : MGraph W → ℝ) :
    poissonGraphMean t (fun G : MGraph V => f (relabel e G)) =
      poissonGraphMean t f := by
  unfold poissonGraphMean poissonMixture
  apply tsum_congr
  intro m
  exact congrArg (fun z => poissonWeight t m * z)
    ((hRelabel V W e q (fun _ => 0)).2.2.2.2.2 m f)

end ThLean.W.S541S

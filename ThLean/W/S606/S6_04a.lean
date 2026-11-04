module

public import ThLean.BP.S6.Foundation

@[expose] public section

set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S606

private abbrev edgePairFintypeK (n : ℕ) : Fintype (Edge n) :=
  @Subtype.fintype (Sym2 (Fin n)) (fun e => ∀ v : Fin n, e ≠ s(v, v))
    (fun a =>
      @Fintype.decidableForallFintype (Fin n)
        (fun v => @Ne (Sym2 (Fin n)) a (@Sym2.mk (Fin n) v v))
        (fun a_1 =>
          @instDecidableNot (@Eq (Sym2 (Fin n)) a (@Sym2.mk (Fin n) a_1 a_1))
            (@Sym2.instDecidableEq (Fin n)
              (fun x y => Classical.propDecidable (@Eq (Fin n) x y)) a
              (@Sym2.mk (Fin n) a_1 a_1)))
        (Fin.fintype n))
    (@Sym2.instFintype (Fin n) (Fin.fintype n))

private abbrev edgePairFintypeS6 (n : ℕ) : Fintype (Edge n) :=
  @Subtype.fintype (Sym2 (Fin n)) (fun e => ∀ v : Fin n, e ≠ s(v, v))
    (fun e => Nat.decidableForallFin (fun v : Fin n => e ≠ s(v, v)))
    Sym2.instFintype

private def frozenSym {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V)
    (e : Sym2 V) : Prop :=
  ∃ a b, e = s(a, b) ∧ Frozen q G a b

private theorem frozen_symm {V : Type*} [Fintype V] {q : ℕ} {G : MGraph V}
    {a b : V} (h : Frozen q G a b) : Frozen q G b a := by
  rcases h with ⟨hc, hf⟩
  exact ⟨hc, fun σ hs => (hf σ hs).symm⟩

private theorem frozenSym_mk_iff {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V)
    (a b : V) : frozenSym q G (s(a, b)) ↔ Frozen q G a b := by
  constructor
  · rintro ⟨a', b', hab, hf⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst a'
      subst b'
      exact hf
    · subst a'
      subst b'
      exact frozen_symm hf
  · intro hf
    exact ⟨a, b, rfl, hf⟩

private theorem indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split_ifs <;> norm_num

private theorem indicator_mono {P Q : Prop} (h : P → Q) :
    indicator P ≤ indicator Q := by
  by_cases hp : P
  · have hq : Q := h hp
    simp [indicator, hp, hq]
  · unfold indicator
    simp only [hp, if_false]
    split_ifs <;> norm_num

private theorem indicator_partition (P : Prop) (K x : ℕ) :
    indicator P = indicator (P ∧ K ≤ x) + indicator (P ∧ x < K) := by
  by_cases hp : P
  · by_cases hx : K ≤ x
    · have hn : ¬ x < K := Nat.not_lt_of_ge hx
      simp [indicator, hp, hx, hn]
    · have hx' : x < K := Nat.lt_of_not_ge hx
      simp [indicator, hp, hx, hx']
  · simp [indicator, hp]

private theorem degree_le_edgeCount {V : Type*} [Fintype V] (G : MGraph V) (u : V) :
    degree G u ≤ edgeCount G := by
  unfold degree edgeCount
  exact Finset.sum_le_sum (fun e he => by
    by_cases ht : Touches u e
    · simp [ht]
    · simp [ht])

private theorem indicator_and_mul (P Q : Prop) :
    indicator (P ∧ Q) = indicator P * indicator Q := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [indicator, hp, hq]

private theorem uniformMean_instance_irrel {A : Type*} (i₁ i₂ : Fintype A)
    (f : A → ℝ) : @uniformMean A i₁ f = @uniformMean A i₂ f := by
  unfold uniformMean
  have hu : @Finset.univ A i₁ = @Finset.univ A i₂ := by
    ext x
    simp
  have hc : @Fintype.card A i₁ = @Fintype.card A i₂ := by
    change (@Finset.univ A i₁).card = (@Finset.univ A i₂).card
    rw [hu]
  rw [hu, hc]

private theorem uniformProb_le_one {A : Type*} [Fintype A] (P : A → Prop)
    (hne : Nonempty A) : uniformProb P ≤ 1 := by
  have hcard : 0 < (Fintype.card A : ℝ) := by
    have hp : 0 < Fintype.card A := Fintype.card_pos_iff.mpr hne
    exact_mod_cast hp
  unfold uniformProb uniformMean
  apply (div_le_iff₀ hcard).2
  have hsum : (∑ a, indicator (P a)) ≤ (Fintype.card A : ℝ) := by
    calc
      _ ≤ ∑ _a : A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        unfold indicator
        split_ifs <;> norm_num
      _ = _ := by simp
  simpa using hsum

private theorem indicator_symm_pair {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V)
    (a b : V) :
    indicator (a ≠ b ∧ Frozen q G a b) =
      indicator (a ≠ b) * indicator (frozenSym q G (s(a, b))) := by
  rw [indicator_and_mul, frozenSym_mk_iff]

theorem S6_04aStatement_of_deps (h03 : S6_03Statement) :
    S6_04aStatement := by
  classical
  intro n q hn hq G j K hK
  let D : ℝ := (n : ℝ) * ((n : ℝ) - 1)
  have hD : 0 < D := by
    have hnR : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n by omega)
    dsimp [D]
    nlinarith
  have hfull0 : 0 ≤ kappaDegree q j G := by
    unfold kappaDegree
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro u hu
      apply Finset.sum_nonneg
      intro v hv
      exact indicator_nonneg _
    · exact le_of_lt (by simpa [Fintype.card_fin, D] using hD)
  have hnp0 : 0 ≤ kappaDegreeNP q K j G := by
    unfold kappaDegreeNP
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro u hu
      apply Finset.sum_nonneg
      intro v hv
      exact indicator_nonneg _
    · exact le_of_lt (by simpa [Fintype.card_fin, D] using hD)
  have hpiv0 : 0 ≤ kappaDegreePiv q K j G := by
    unfold kappaDegreePiv
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro u hu
      apply Finset.sum_nonneg
      intro v hv
      exact indicator_nonneg _
    · exact le_of_lt (by simpa [Fintype.card_fin, D] using hD)
  have hsumPart :
      (∑ u : Fin n, ∑ v : Fin n,
        indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j)) =
      (∑ u : Fin n, ∑ v : Fin n,
        indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j ∧
          K ≤ nonpivotalCount q G u v)) +
      (∑ u : Fin n, ∑ v : Fin n,
        indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j ∧
          nonpivotalCount q G u v < K)) := by
    calc
      _ = ∑ u : Fin n, ∑ v : Fin n,
          (indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j ∧
              K ≤ nonpivotalCount q G u v) +
            indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j ∧
              nonpivotalCount q G u v < K)) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        simpa only [and_assoc] using
          (indicator_partition (u ≠ v ∧ Frozen q G u v ∧ degree G u = j)
            K (nonpivotalCount q G u v))
      _ = _ := by simp_rw [Finset.sum_add_distrib]
  have hpart : kappaDegree q j G = kappaDegreeNP q K j G + kappaDegreePiv q K j G := by
    unfold kappaDegree kappaDegreeNP kappaDegreePiv
    rw [show ((Fintype.card (Fin n) : ℝ) *
        ((Fintype.card (Fin n) : ℝ) - 1)) = D by simp [D, Fintype.card_fin]]
    rw [← add_div]
    exact congrArg (fun x : ℝ => x / D) hsumPart
  have hbase_le :
      (∑ u : Fin n, ∑ v : Fin n,
        indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j)) ≤
      ∑ u : Fin n, ∑ v : Fin n, indicator (u ≠ v ∧ Frozen q G u v) := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    apply indicator_mono
    rintro ⟨hne, hf, hj⟩
    exact ⟨hne, hf⟩
  have hpairProb :
      @uniformProb (Edge n) (edgePairFintypeK n) (FrozenPair q G) =
        @uniformMean (Edge n) (edgePairFintypeK n)
          (fun e : Edge n => indicator (frozenSym q G e.val)) := by
    unfold uniformProb uniformMean
    rfl
  have hmean := (h03 n hn).2.1
    (fun e : Sym2 (Fin n) => indicator (frozenSym q G e))
  have hmeanCurrent :
      @uniformMean (Edge n) (edgePairFintypeK n)
        (fun e => indicator (frozenSym q G e.val)) =
      (∑ a : Fin n, ∑ b : Fin n,
        indicator (a ≠ b) * indicator (frozenSym q G (s(a, b)))) / D := by
    calc
      @uniformMean (Edge n) (edgePairFintypeK n)
          (fun e => indicator (frozenSym q G e.val)) =
          @uniformMean (Edge n) (edgePairFintypeS6 n)
            (fun e => indicator (frozenSym q G e.val)) :=
        uniformMean_instance_irrel (edgePairFintypeK n) (edgePairFintypeS6 n) _
      _ = _ := by simpa [D] using hmean
  have hsumFrozen :
      (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b ∧ Frozen q G a b)) =
      ∑ a : Fin n, ∑ b : Fin n,
        indicator (a ≠ b) * indicator (frozenSym q G (s(a, b))) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact indicator_symm_pair q G a b
  have hkappa : kappa q G =
      (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b ∧ Frozen q G a b)) / D := by
    unfold kappa
    calc
      @uniformProb (Edge n) (edgePairFintypeK n) (FrozenPair q G) =
          @uniformMean (Edge n) (edgePairFintypeK n)
            (fun e : Edge n => indicator (frozenSym q G e.val)) := hpairProb
      _ = (∑ a : Fin n, ∑ b : Fin n,
            indicator (a ≠ b) * indicator (frozenSym q G (s(a, b)))) /
            ((n : ℝ) * ((n : ℝ) - 1)) := by simpa [D] using hmeanCurrent
      _ = _ := by rw [← hsumFrozen]
  have hbound : kappaDegree q j G ≤ kappa q G := by
    unfold kappaDegree
    rw [show ((Fintype.card (Fin n) : ℝ) *
        ((Fintype.card (Fin n) : ℝ) - 1)) = D by simp [D, Fintype.card_fin]]
    rw [hkappa]
    exact (div_le_div_iff_of_pos_right hD).2 hbase_le
  have hnonempty : Nonempty (Edge n) := by
    let z : Fin n := ⟨0, by omega⟩
    let o : Fin n := ⟨1, by omega⟩
    have h01 : z ≠ o := by
      intro he
      have hv := congrArg Fin.val he
      dsimp [z, o] at hv
      omega
    have e : Edge n := ⟨s(z, o), by
      intro v hv
      have hp := (Sym2.eq_iff).1 hv
      rcases hp with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact h01 (h0.trans h1.symm)
      · exact h01 (h0.trans h1.symm)⟩
    exact ⟨e⟩
  have hkappa1 : kappa q G ≤ 1 := by
    unfold kappa
    exact @uniformProb_le_one (Edge n) (edgePairFintypeK n)
      (FrozenPair q G) hnonempty
  have hsupport : edgeCount G < j →
      kappaDegree q j G = 0 ∧ kappaDegreeNP q K j G = 0 ∧
        kappaDegreePiv q K j G = 0 := by
    intro hedge
    have hdeg : ∀ u : Fin n, degree G u < j := by
      intro u
      exact lt_of_le_of_lt (degree_le_edgeCount G u) hedge
    have hzeroFull :
        (∑ u : Fin n, ∑ v : Fin n,
          indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      have hne : degree G u ≠ j := (hdeg u).ne
      simp [indicator, hne]
    have hzeroNP :
        (∑ u : Fin n, ∑ v : Fin n,
          indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j ∧
            K ≤ nonpivotalCount q G u v)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      have hne : degree G u ≠ j := (hdeg u).ne
      simp [indicator, hne]
    have hzeroPiv :
        (∑ u : Fin n, ∑ v : Fin n,
          indicator (u ≠ v ∧ Frozen q G u v ∧ degree G u = j ∧
            nonpivotalCount q G u v < K)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      have hne : degree G u ≠ j := (hdeg u).ne
      simp [indicator, hne]
    refine ⟨?_, ?_, ?_⟩
    · unfold kappaDegree
      rw [hzeroFull]
      simp
    · unfold kappaDegreeNP
      rw [hzeroNP]
      simp
    · unfold kappaDegreePiv
      rw [hzeroPiv]
      simp
  exact ⟨hfull0, hnp0, hpiv0, hpart, hbound, hkappa1, hsupport⟩

end ThLean.W.S606

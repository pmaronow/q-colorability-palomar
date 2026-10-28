import ThLean.BP.S5.Identification

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

namespace ThLean.W.S518
open ThresholdFoundations
open ThLean.BP.S5

private lemma uniformMean_nonneg {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  unfold uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg fun a _ => hf a
  · exact Nat.cast_nonneg _

private lemma uniformProb_nonneg {A : Type} [Fintype A] [Nonempty A]
    (P : A → Prop) : 0 ≤ uniformProb P := by
  unfold uniformProb
  apply uniformMean_nonneg
  intro a
  unfold indicator
  split_ifs <;> norm_num

private lemma uniformMeanENN_ofReal {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    uniformMeanENN (fun a => ENNReal.ofReal (f a)) = ENNReal.ofReal (uniformMean f) := by
  have hcard : (0 : ℝ) < (Fintype.card A : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ‹Nonempty A›)
  unfold uniformMeanENN uniformMean
  calc
    (∑ a, ENNReal.ofReal (f a)) / (Fintype.card A : ℝ≥0∞) =
        ENNReal.ofReal (∑ a, f a) / ENNReal.ofReal (Fintype.card A : ℝ) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a)]
          simp
    _ = ENNReal.ofReal ((∑ a, f a) / (Fintype.card A : ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos hcard]

private lemma uniformMeanENN_indicator {A : Type} [Fintype A] [Nonempty A]
    (P : A → Prop) (d : ∀ a, Decidable (P a)) :
    uniformMeanENN (fun a => @ite ℝ≥0∞ (P a) (d a) 1 0) =
      ENNReal.ofReal (uniformProb P) := by
  have h := uniformMeanENN_ofReal (fun a => indicator (P a)) (by
    intro a
    unfold indicator
    split_ifs <;> norm_num)
  calc
    uniformMeanENN (fun a => @ite ℝ≥0∞ (P a) (d a) 1 0) =
        uniformMeanENN (fun a => ENNReal.ofReal (indicator (P a))) := by
          congr 1
          funext a
          by_cases hP : P a <;> simp [hP, indicator]
    _ = ENNReal.ofReal (uniformProb P) := by
          simpa [uniformProb] using h

private lemma nestedUniformMeanENN_indicator
    {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (P : A → B → Prop) (d : ∀ a b, Decidable (P a b)) :
    uniformMeanENN (fun a => uniformMeanENN (fun b => @ite ℝ≥0∞ (P a b) (d a b) 1 0)) =
      ENNReal.ofReal (uniformMean (fun a => uniformProb (P a))) := by
  calc
    uniformMeanENN (fun a => uniformMeanENN (fun b => @ite ℝ≥0∞ (P a b) (d a b) 1 0)) =
        uniformMeanENN (fun a => ENNReal.ofReal (uniformProb (P a))) := by
          congr 1
          funext a
          exact uniformMeanENN_indicator (P a) (d a)
    _ = ENNReal.ofReal (uniformMean (fun a => uniformProb (P a))) :=
      uniformMeanENN_ofReal _ (fun a => uniformProb_nonneg (P a))

private def identificationAdvanceTerm {V : Type} [Fintype V]
    (q D m : ℕ) : ℝ≥0∞ :=
  uniformMeanENN (fun x : EdgeTuple V m =>
    uniformMeanENN (fun Z : UniformSubset V D =>
      if Colorable q (tupleGraph x) ∧ ¬ Colorable q (identify (tupleGraph x) Z.val)
      then (1 : ℝ≥0∞) else 0))

private def genericPairFintype {V : Type} [Fintype V] : Fintype (Pair V) :=
  @Subtype.fintype (Sym2 V) (fun e => ∀ v : V, e ≠ s(v, v))
    (fun e => Fintype.decidableForallFintype) Sym2.instFintype

private def genericEdgeTupleFintype {V : Type} [Fintype V] (m : ℕ) :
    Fintype (EdgeTuple V m) := by
  letI : Fintype (Pair V) := genericPairFintype
  infer_instance

private lemma identificationAdvance_eq_tsum {V : Type} [Fintype V] (q D : ℕ) :
    identificationAdvance (V := V) q D =
      ∑' m : ℕ, identificationAdvanceTerm (V := V) q D m := by
  rfl

private lemma identificationAdvanceTerm_eq {V : Type} [Fintype V]
    (q D m : ℕ) [Nonempty (Pair V)] [Nonempty (UniformSubset V D)] :
    identificationAdvanceTerm (V := V) q D m =
      ENNReal.ofReal (@uniformMean (EdgeTuple V m) (genericEdgeTupleFintype m) (fun x =>
        identificationFailureProbability q D (tupleGraph x))) := by
  unfold identificationAdvanceTerm
  letI : Fintype (EdgeTuple V m) := genericEdgeTupleFintype (V := V) m
  let d : ∀ x : EdgeTuple V m, ∀ Z : UniformSubset V D,
      Decidable (Colorable q (tupleGraph x) ∧
        ¬ Colorable q (identify (tupleGraph x) Z.val)) := fun x Z => inferInstance
  change uniformMeanENN (fun x => uniformMeanENN (fun Z =>
    @ite ℝ≥0∞ _ (d x Z) 1 0)) =
    ENNReal.ofReal (uniformMean (fun x =>
      identificationFailureProbability q D (tupleGraph x)))
  simpa [identificationFailureProbability] using
    (nestedUniformMeanENN_indicator
      (A := EdgeTuple V m) (B := UniformSubset V D)
      (fun x Z => Colorable q (tupleGraph x) ∧
        ¬ Colorable q (identify (tupleGraph x) Z.val)) d)

private lemma uniformMean_fintype_irrel
    (hFinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0})
    {A : Type} (i j : Fintype A) (hA : Nonempty A) (f : A → ℝ) :
    @uniformMean A i f = @uniformMean A j f := by
  have h := @hFinite.1 A A i j hA hA (Equiv.refl A) f
  simpa using h

private lemma pairFin_nonempty (N : ℕ) (hN : 2 ≤ N) :
    Nonempty (Pair (Fin N)) := by
  let z : Fin N := ⟨0, by omega⟩
  let o : Fin N := ⟨1, by omega⟩
  have hzo : z ≠ o := by
    intro h
    have hh := congrArg Fin.val h
    norm_num at hh
  have hp : Pair (Fin N) := ⟨s(z, o), by
    intro v hv
    rcases Sym2.eq_iff.mp hv with h | h
    · exact hzo (h.1.trans h.2.symm)
    · exact hzo (h.1.trans h.2.symm)
    ⟩
  exact ⟨hp⟩

private lemma uniformSubsetFin_nonempty (N D : ℕ) (hDN : D ≤ N) :
    Nonempty (UniformSubset (Fin N) D) := by
  let S : Finset (Fin N) := Finset.univ.map (Fin.castLEEmb hDN)
  have hS : S.card = D := by simp [S]
  exact ⟨⟨S, hS⟩⟩

private lemma infiniteHittingProbability_zero_of_lifetime
    (hLife : ThresholdFoundations.PreLifetimeStatement.{0})
    (q N : ℕ) (hq : 3 ≤ q) (hN : 2 * q ≤ N) :
    infiniteHittingProbability (V := Fin N) q = 0 := by
  have hN2 : 2 ≤ N := by omega
  have hcard : 2 ≤ Fintype.card (Fin N) := by simpa using hN2
  have hlife := (hLife (Fin N) q hq hcard).1 (0 : MGraph (Fin N)) (by simp [Loopless])
  have hfiniteLife := hlife.2.2.2.2 (by simpa using hN)
  have hsurv : Summable (processSurvival (V := Fin N) q) := by
    change Summable (survival (V := Fin N) q (0 : MGraph (Fin N)))
    exact hfiniteLife.2.2.1
  have hsurvZero : Tendsto (processSurvival (V := Fin N) q) atTop (𝓝 0) :=
    hsurv.tendsto_atTop_zero
  have hsurvNonneg : ∀ m, 0 ≤ processSurvival (V := Fin N) q m := by
    intro m
    unfold processSurvival survival uniformProb uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x hx
      unfold indicator
      split_ifs <;> norm_num
    · exact Nat.cast_nonneg _
  have hInf : infiniteHittingProbability (V := Fin N) q = 0 := by
    unfold infiniteHittingProbability
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
      (s := Set.range (processSurvival (V := Fin N) q))
    · exact ⟨processSurvival (V := Fin N) q 0, ⟨0, rfl⟩⟩
    · intro a ha
      rcases ha with ⟨m, rfl⟩
      exact hsurvNonneg m
    · intro b hb
      have hevent : ∀ᶠ m : ℕ in atTop, processSurvival (V := Fin N) q m < b :=
        (tendsto_order.1 hsurvZero).2 b hb
      obtain ⟨M, hM⟩ := eventually_atTop.1 hevent
      exact ⟨processSurvival (V := Fin N) q M, ⟨M, rfl⟩, hM M le_rfl⟩
  exact hInf

private lemma advanceBound_of_17D
    (h17D : ThLean.BP.S5.S5_17DStatement)
    (q N D : ℕ) (hq : 3 ≤ q) (hN : 2 * q ≤ N)
    (hD1 : 1 ≤ D) (hDN : D ≤ N) :
    identificationAdvance (V := Fin N) q D < ⊤ ∧
      advanceReal q N D ≤ lifetimeConstant q * N := by
  have hbound : identificationAdvance (V := Fin N) q D ≤
      ENNReal.ofReal (lifetimeConstant q * (Fintype.card (Fin N) : ℝ)) :=
    h17D (Fin N) q hq (by simpa using hN) D hD1 (by simpa using hDN)
  have hconst : 0 ≤ lifetimeConstant q * (N : ℝ) := by
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    unfold lifetimeConstant
    positivity
  constructor
  · exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  · unfold advanceReal
    calc
      (identificationAdvance (V := Fin N) q D).toReal ≤
          (ENNReal.ofReal (lifetimeConstant q * (Fintype.card (Fin N) : ℝ))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      _ = lifetimeConstant q * N := by simp [hconst]

private lemma advanceSeries_of_finite
    (hFinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0})
    (q N D : ℕ) (hN : 2 ≤ N) (hDN : D ≤ N)
    (hfinite : identificationAdvance (V := Fin N) q D < ⊤) :
    0 ≤ advanceReal q N D ∧
    HasSum (fun m => uniformMean (fun x : EdgeTuple (Fin N) m =>
      identificationFailureProbability q D (tupleGraph x))) (advanceReal q N D) := by
  letI : Nonempty (Pair (Fin N)) := pairFin_nonempty N hN
  letI : Nonempty (UniformSubset (Fin N) D) := uniformSubsetFin_nonempty N D hDN
  let advanceTerm : ℕ → ℝ≥0∞ := identificationAdvanceTerm (V := Fin N) q D
  have hadvanceDef : identificationAdvance (V := Fin N) q D = ∑' m : ℕ, advanceTerm m :=
    identificationAdvance_eq_tsum q D
  have htermNonneg (m : ℕ) :
      0 ≤ uniformMean (fun x : EdgeTuple (Fin N) m =>
        identificationFailureProbability q D (tupleGraph x)) := by
    unfold uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x hx
      unfold identificationFailureProbability uniformProb uniformMean
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro Z hZ
        unfold indicator
        split_ifs <;> norm_num
      · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  have htermFinite (m : ℕ) : advanceTerm m ≠ ⊤ := by
    change identificationAdvanceTerm (V := Fin N) q D m ≠ ⊤
    rw [identificationAdvanceTerm_eq q D m]
    exact ENNReal.ofReal_ne_top
  have htotalNeTop : (∑' m : ℕ, advanceTerm m) ≠ ⊤ := by
    rw [← hadvanceDef]
    exact ne_of_lt hfinite
  have hRealTerm (m : ℕ) :
      uniformMean (fun x : EdgeTuple (Fin N) m =>
        identificationFailureProbability q D (tupleGraph x)) = (advanceTerm m).toReal := by
    let A := EdgeTuple (Fin N) m
    let genericFt : Fintype A := genericEdgeTupleFintype (V := Fin N) m
    let targetPairFt : Fintype (Pair (Fin N)) :=
      @Subtype.fintype (Sym2 (Fin N)) (fun e => ∀ v : Fin N, e ≠ s(v, v))
        (fun e => Nat.decidableForallFin (fun v : Fin N => e ≠ s(v, v))) Sym2.instFintype
    let targetFt : Fintype A :=
      @Pi.instFintype (Fin m) (fun _ => Pair (Fin N))
        (inferInstance : DecidableEq (Fin m)) (Fin.fintype m) (fun _ => targetPairFt)
    let f : A → ℝ := fun x => identificationFailureProbability q D (tupleGraph x)
    have hdata := identificationAdvanceTerm_eq (V := Fin N) q D m
    have hmeanEq : @uniformMean A genericFt f = @uniformMean A targetFt f :=
      uniformMean_fintype_irrel hFinite genericFt targetFt
        ⟨fun _ => Classical.choice (pairFin_nonempty N hN)⟩ f
    have hgenericNonneg : 0 ≤ @uniformMean A genericFt f := by
      rw [hmeanEq]
      exact htermNonneg m
    have hcalc : @uniformMean A targetFt f = (advanceTerm m).toReal := by
      calc
        @uniformMean A targetFt f = @uniformMean A genericFt f := hmeanEq.symm
        _ = (ENNReal.ofReal (@uniformMean A genericFt f)).toReal :=
          (ENNReal.toReal_ofReal hgenericNonneg).symm
        _ = (advanceTerm m).toReal := congrArg ENNReal.toReal hdata.symm
    exact hcalc
  have hrealSum :
      (∑' m : ℕ, uniformMean (fun x : EdgeTuple (Fin N) m =>
        identificationFailureProbability q D (tupleGraph x))) = advanceReal q N D := by
    calc
      _ = ∑' m : ℕ, (advanceTerm m).toReal := tsum_congr hRealTerm
      _ = (∑' m : ℕ, advanceTerm m).toReal := (ENNReal.tsum_toReal_eq htermFinite).symm
      _ = advanceReal q N D := by rw [← hadvanceDef]; rfl
  have hsumToReal : Summable (fun m : ℕ => (advanceTerm m).toReal) :=
    ENNReal.summable_toReal htotalNeTop
  have hsumFailure : Summable (fun m : ℕ => uniformMean (fun x : EdgeTuple (Fin N) m =>
      identificationFailureProbability q D (tupleGraph x))) :=
    hsumToReal.congr (fun m => (hRealTerm m).symm)
  exact ⟨ENNReal.toReal_nonneg, hsumFailure.hasSum_iff.mpr hrealSum⟩

/-- The 17B estimate and series, from the generic advance and lifetime contracts. -/
theorem S5_17BStatement_of_deps
    (h17D : ThLean.BP.S5.S5_17DStatement)
    (hLife : ThresholdFoundations.PreLifetimeStatement.{0})
    (hFinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0}) :
    ThLean.BP.S5.S5_17BStatement := by
  intro q N D hq hN hD1 hDN
  have hInf := infiniteHittingProbability_zero_of_lifetime hLife q N hq hN
  have hbound := advanceBound_of_17D h17D q N D hq hN hD1 hDN
  have hseries := advanceSeries_of_finite hFinite q N D (by omega) hDN hbound.1
  exact ⟨hInf, hbound.1, hseries.1, hbound.2, hseries.2⟩

end ThLean.W.S518

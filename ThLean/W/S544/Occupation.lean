module

public import ThLean.Contrib.S544.Occupation

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S544
open ThresholdFoundations ThLean.BP.S5 ThLean.Contrib.S544
variable {n : ℕ}

private lemma uniformMean_fintype_independent {A : Type*}
    (i j : Fintype A) (f : A → ℝ) :
    @uniformMean A i f = @uniformMean A j f := by
  unfold uniformMean
  have hs : (@Finset.univ A i).sum f = (@Finset.univ A j).sum f := by
    exact @Fintype.sum_equiv A A ℝ i j inferInstance (Equiv.refl A) f f
      (fun _ => rfl)
  have hc := @Fintype.card_congr A A i j (Equiv.refl A)
  rw [hs, hc]

private lemma uniformMeanENN_fintype_independent {A : Type*}
    (i j : Fintype A) (f : A → ℝ≥0∞) :
    @uniformMeanENN A i f = @uniformMeanENN A j f := by
  unfold uniformMeanENN
  have hs : (@Finset.univ A i).sum f = (@Finset.univ A j).sum f := by
    exact @Fintype.sum_equiv A A ℝ≥0∞ i j inferInstance (Equiv.refl A) f f
      (fun _ => rfl)
  have hc := @Fintype.card_congr A A i j (Equiv.refl A)
  rw [hs, hc]

private lemma ofReal_uniformMean {A : Type*} [Fintype A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (uniformMean f) =
      uniformMeanENN (fun a => ENNReal.ofReal (f a)) := by
  by_cases hA : IsEmpty A
  · letI := hA
    simp [uniformMean, uniformMeanENN]
  · have hcard : (0 : ℝ) < (Fintype.card A : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (not_isEmpty_iff.mp hA))
    unfold uniformMean uniformMeanENN
    rw [ENNReal.ofReal_div_of_pos hcard]
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a)]
    simp [ENNReal.ofReal_natCast]

private lemma ofReal_pairUniformProb {V : Type*} [Fintype V]
    (P : Pair V → Prop) :
    ENNReal.ofReal (uniformProb P) =
      uniformMeanENN (fun a => if P a then 1 else 0) := by
  unfold uniformProb
  rw [ofReal_uniformMean]
  · congr 1
    funext a
    by_cases h : P a <;> simp [indicator, h]
  · intro a
    unfold indicator
    split_ifs <;> positivity

private lemma lowKappa_nonneg (q D : ℕ) (G : MGraph (Fin n)) :
    0 ≤ lowKappa q D G := by
  unfold lowKappa kappaKind uniformProb uniformMean indicator
  apply div_nonneg
  · exact Finset.sum_nonneg fun e _ => by split_ifs <;> positivity
  · positivity

private lemma lowKappa_le_kappa (q D : ℕ) (G : MGraph (Fin n)) :
    lowKappa q D G ≤ kappa q G := by
  unfold lowKappa kappa kappaKind uniformProb uniformMean indicator
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro e he
  by_cases hF : FrozenPair q G e <;> by_cases hL : lowEdge G D e <;>
    simp [hF, hL]

private lemma lowObservable_nonneg (q D : ℕ) (y : ℝ) (G : MGraph (Fin n)) :
    0 ≤ lowObservable q D y G := by
  unfold lowObservable indicator
  split_ifs <;> positivity [lowKappa_nonneg (n := n) q D G]

private lemma lowObservable_enn (q D : ℕ) (y : ℝ) (G : MGraph (Fin n)) :
    ENNReal.ofReal (lowObservable q D y G) =
      kappaKindENN q (fun F e => lowEdge F D e) G *
        (if ENNReal.ofReal y < lifetime q G then 1 else 0) := by
  unfold lowObservable
  rw [ENNReal.ofReal_mul (lowKappa_nonneg (n := n) q D G)]
  by_cases hLife : ENNReal.ofReal y < lifetime q G
  · simp only [indicator, if_pos hLife, ENNReal.ofReal_one, mul_one]
    unfold lowKappa kappaKind kappaKindENN
    rw [ofReal_pairUniformProb]
    congr 1
    funext e
    by_cases he : FrozenPair q G e ∧ (fun F e => lowEdge F D e) G e <;> simp [he]
  · simp only [indicator, if_neg hLife, ENNReal.ofReal_zero, mul_zero]

private lemma lowSequence_nonneg (q D : ℕ) (y : ℝ) (m : ℕ) :
    0 ≤ uniformMean (fun x : EdgeTuple (Fin n) m =>
      lowObservable q D y (tupleGraph x)) := by
  unfold uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => lowObservable_nonneg q D y (tupleGraph x)
  · positivity

private lemma lowSequence_le_kappa (q D : ℕ) (y : ℝ) (m : ℕ) :
    uniformMean (fun x : EdgeTuple (Fin n) m =>
      lowObservable q D y (tupleGraph x)) ≤
      graphMean (V := Fin n) m (fun G => kappa q G) := by
  have hmean : graphMean (V := Fin n) m (fun G => kappa q G) =
      uniformMean (fun x : EdgeTuple (Fin n) m => kappa q (tupleGraph x)) := by
    unfold graphMean
    exact uniformMean_fintype_independent _ _ _
  rw [hmean]
  unfold uniformMean
  have hsum :
      (∑ x : EdgeTuple (Fin n) m, lowObservable q D y (tupleGraph x)) ≤
      ∑ x : EdgeTuple (Fin n) m, kappa q (tupleGraph x) := by
    apply Finset.sum_le_sum
    intro x hx
    have hk0 : 0 ≤ kappa q (tupleGraph x) :=
      le_trans (lowKappa_nonneg q D (tupleGraph x))
        (lowKappa_le_kappa q D (tupleGraph x))
    unfold lowObservable indicator
    split_ifs with hLife
    · simpa using lowKappa_le_kappa q D (tupleGraph x)
    · simpa using hk0
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

private lemma lowSequence_summable_of_hazard (hPreHazard : PreHazardStatement)
    (q n D : ℕ) (hq : 3 ≤ q) (hn : 2 * q + 1 ≤ n) (y : ℝ) :
    Summable (fun m => uniformMean (fun x : EdgeTuple (Fin n) m =>
      lowObservable q D y (tupleGraph x))) := by
  have hnn : ∀ m, 0 ≤ uniformMean (fun x : EdgeTuple (Fin n) m =>
      lowObservable q D y (tupleGraph x)) := fun m => lowSequence_nonneg q D y m
  have hbudget : ∀ J : Finset ℕ,
      (∑ m ∈ J, uniformMean (fun x : EdgeTuple (Fin n) m =>
        lowObservable q D y (tupleGraph x))) ≤ 1 := by
    intro J
    have hHaz := hPreHazard q n hq (by omega)
    calc
      (∑ m ∈ J, uniformMean (fun x : EdgeTuple (Fin n) m =>
        lowObservable q D y (tupleGraph x))) ≤
        ∑ m ∈ J, graphMean (V := Fin n) m (fun G => kappa q G) := by
          apply Finset.sum_le_sum
          intro m hm
          exact lowSequence_le_kappa q D y m
      _ ≤ ∑ m ∈ J, hittingMass (V := Fin n) q m := by
        have h := hHaz.2.1 J (fun _ _ => (1 : ℝ))
          (by intro m hm G; constructor <;> norm_num)
        simpa only [one_mul] using h
      _ ≤ 1 := hHaz.2.2 J
  exact summable_of_sum_le hnn hbudget

private lemma lowTerminalENN_disintegration (hPreTerminal : PreTerminalStatement)
    (q n D : ℕ) (hq : 3 ≤ q) (hn : 2 * q + 1 ≤ n) (y : ℝ) :
    terminalMeanENN (V := Fin n) q
      (fun G e => @ite ℝ≥0∞ (lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G)
        (Classical.propDecidable _) 1 0) =
    ∑' m, ENNReal.ofReal (uniformMean (fun x : EdgeTuple (Fin n) m =>
      lowObservable q D y (tupleGraph x))) := by
  let A : MGraph (Fin n) → Pair (Fin n) → Prop := fun G e => lowEdge G D e
  let w : ℕ → MGraph (Fin n) → ℝ≥0∞ := fun _ G =>
    if ENNReal.ofReal y < lifetime q G then 1 else 0
  have hfun (m : ℕ) :
      (fun G e => if A G e then w m G else 0) =
      (fun G e => @ite ℝ≥0∞ (lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G)
        (Classical.propDecidable _) 1 0) := by
    funext G e
    by_cases hA : A G e <;> by_cases hLife : ENNReal.ofReal y < lifetime q G <;>
      simp [A, w, hA, hLife]
  have hleft :
      terminalMeanENN (V := Fin n) q
        (fun G e => @ite ℝ≥0∞ (lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G)
          (Classical.propDecidable _) 1 0) =
      terminalRangeENN (V := Fin n) q 0 ⊤
        (fun m G e => if A G e then w m G else 0) := by
    unfold terminalMeanENN terminalRangeENN
    apply tsum_congr
    intro m
    have htop : (m : WithTop ℕ) < ⊤ := WithTop.coe_lt_top m
    simpa [htop] using (congrArg (terminalStepENN q m) (hfun m).symm)
  have hpre := hPreTerminal.1 q n hq (by omega) A w 0 ⊤
  have hpre' :
      terminalRangeENN (V := Fin n) q 0 ⊤
        (fun m G e => if A G e then w m G else 0) =
      ∑' m, graphMeanENN m (fun G => kappaKindENN q A G * w m G) := by
    calc
      terminalRangeENN (V := Fin n) q 0 ⊤
          (fun m G e => if A G e then w m G else 0) =
        ∑' m : ℕ, if 0 ≤ m ∧ (m : WithTop ℕ) < ⊤ then
          graphMeanENN m (fun G => kappaKindENN q A G * w m G) else 0 := hpre
      _ = ∑' m, graphMeanENN m (fun G => kappaKindENN q A G * w m G) := by
        apply tsum_congr
        intro m
        have htop : (m : WithTop ℕ) < ⊤ := WithTop.coe_lt_top m
        simp [htop]
  have hmean (m : ℕ) :
      graphMeanENN m (fun G => kappaKindENN q A G * w m G) =
      ENNReal.ofReal (uniformMean (fun x : EdgeTuple (Fin n) m =>
        lowObservable q D y (tupleGraph x))) := by
    unfold graphMeanENN
    rw [ofReal_uniformMean]
    · have hfunc :
        (fun x : EdgeTuple (Fin n) m => kappaKindENN q A (tupleGraph x) * w m (tupleGraph x)) =
        (fun x => ENNReal.ofReal (lowObservable q D y (tupleGraph x))) := by
          funext x
          symm
          simpa [A, w] using lowObservable_enn q D y (tupleGraph x)
      rw [hfunc]
      exact uniformMeanENN_fintype_independent _ _ _
    · intro x
      exact lowObservable_nonneg q D y (tupleGraph x)
  calc
    terminalMeanENN (V := Fin n) q
        (fun G e => @ite ℝ≥0∞ (lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G)
          (Classical.propDecidable _) 1 0) =
      terminalRangeENN (V := Fin n) q 0 ⊤ (fun m G e => if A G e then w m G else 0) := hleft
    _ = ∑' m, graphMeanENN m (fun G => kappaKindENN q A G * w m G) := hpre'
    _ = ∑' m, ENNReal.ofReal (uniformMean (fun x : EdgeTuple (Fin n) m =>
        lowObservable q D y (tupleGraph x))) := tsum_congr hmean

theorem S5_34ATerminalDisintegrationStatement_of_preconditions
    (hPreTerminal : PreTerminalStatement) (hPreHazard : PreHazardStatement) :
    S5_34ATerminalDisintegrationStatement := by
  intro q n D hq hn y hy
  let a : ℕ → ℝ := fun m => uniformMean (fun x : EdgeTuple (Fin n) m =>
    lowObservable q D y (tupleGraph x))
  have hnonneg : ∀ m, 0 ≤ a m := fun m => by
    exact lowSequence_nonneg q D y m
  have hsummable : Summable a := by
    simpa only [a] using lowSequence_summable_of_hazard hPreHazard q n D hq hn y
  have hterminalENN := lowTerminalENN_disintegration hPreTerminal q n D hq hn y
  have hterminal : lowTerminalProbability (V := Fin n) q D y = ∑' m, a m := by
    unfold lowTerminalProbability terminalProbability
    change (terminalMeanENN (V := Fin n) q
      (fun G e => @ite ℝ≥0∞ (lowEdge G D e ∧ ENNReal.ofReal y < lifetime q G)
        (Classical.propDecidable _) 1 0)).toReal = _
    rw [hterminalENN, ← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable]
    exact ENNReal.toReal_ofReal (tsum_nonneg hnonneg)
  exact ⟨hnonneg, hsummable, hterminal⟩

theorem S5_34ALowTimeOccupationStatement_of_S5_10
    (h10 : S5_10Statement) : S5_34ALowTimeOccupationStatement := by
  intro q n D hq hn y hy a a_nonneg ha
  have hocc := (h10 1 (by norm_num)).2 a a_nonneg ha
  have hrepr : (fun t : ℝ => lowTime q n D y t) = fun t => poissonMixture t a := by
    funext t
    unfold lowTime poissonGraphMean poissonMixture
    apply tsum_congr
    intro m
    simp only [a]
    congr 1
    exact uniformMean_fintype_independent _ _ _
  have hoccInt : IntegrableOn (fun t => poissonMixture t a) (Set.Ici 0) := by
    simpa only [one_mul] using hocc.1
  have hoccEq : (∫ t in Set.Ici (0 : ℝ), poissonMixture t a) = ∑' m, a m := by
    simpa using hocc.2
  have hint : IntegrableOn (lowTime q n D y) (Set.Ici 0) := by
    change IntegrableOn (fun t => lowTime q n D y t) (Set.Ici 0)
    rw [hrepr]
    exact hoccInt
  have hintEq : (∫ t in Set.Ici (0 : ℝ), lowTime q n D y t) = ∑' m, a m := by
    rw [hrepr]
    exact hoccEq
  exact ⟨hint, hintEq⟩

theorem S5_34AStatement_of_terminal_disintegration
    (hTerminal : S5_34ATerminalDisintegrationStatement)
    (h10 : S5_10Statement) : S5_34AStatement := by
  intro q n D hq hn y hy
  let a : ℕ → ℝ := fun m => uniformMean (fun x : EdgeTuple (Fin n) m =>
    lowObservable q D y (tupleGraph x))
  have hparts := hTerminal q n D hq hn y hy
  have hocc := S5_34ALowTimeOccupationStatement_of_S5_10 h10 q n D hq hn y hy
    hparts.1 hparts.2.1
  exact ⟨hparts.2.1, hparts.2.2, hocc.1, hparts.2.2.trans hocc.2.symm⟩

theorem S5_34AStatement_of_deps
    (hPreTerminal : PreTerminalStatement) (hPreHazard : PreHazardStatement)
    (h10 : S5_10Statement) : S5_34AStatement := by
  exact S5_34AStatement_of_terminal_disintegration
    (S5_34ATerminalDisintegrationStatement_of_preconditions hPreTerminal hPreHazard) h10

end ThLean.W.S544

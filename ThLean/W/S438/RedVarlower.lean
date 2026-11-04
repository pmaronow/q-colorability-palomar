module

public import ThLean.BP.S4.Reduction

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S438

open ThresholdFoundations
open ThLean.BP.S4

private noncomputable def quantileTupleFintype {V : Type} [Fintype V] (M : ℕ) :
    Fintype (EdgeTuple V M) := inferInstance

private theorem clippedLower_eq_iff (L U y : ℕ) (hgap : L < U) :
    min U (max L y) = L ↔ y ≤ L := by
  constructor
  · intro h
    by_contra hy
    have hLy : L < y := by omega
    have hmax : max L y = y := max_eq_right (Nat.le_of_lt hLy)
    rw [hmax] at h
    have hlt : L < min U y := by
      by_cases hUy : U ≤ y
      · simpa [min_eq_left hUy] using hgap
      · have hyU : y ≤ U := by omega
        simpa [min_eq_right hyU] using hLy
    omega
  · intro hy
    rw [max_eq_left hy]
    exact min_eq_right (Nat.le_of_lt hgap)

private theorem clippedUpper_eq_iff (L U y : ℕ) (hgap : L < U) :
    min U (max L y) = U ↔ U ≤ y := by
  constructor
  · intro h
    by_contra hy
    have hyU : y < U := by omega
    have hmax : max L y < U := max_lt hgap hyU
    have hle : min U (max L y) ≤ max L y := min_le_right _ _
    rw [h] at hle
    omega
  · intro hy
    have hmax : U ≤ max L y := le_trans hy (le_max_right _ _)
    exact min_eq_left hmax

private theorem uniformMean_fintype_irrel {A : Type} (i j : Fintype A) (f : A → ℝ) :
    @uniformMean A i f = @uniformMean A j f := by
  have hu : @Finset.univ A i = @Finset.univ A j := by
    ext a
    simp
  have hs : (@Finset.univ A i).sum f = (@Finset.univ A j).sum f :=
    congrArg (fun s : Finset A => s.sum f) hu
  have hc : @Fintype.card A i = @Fintype.card A j := by
    change (@Finset.univ A i).card = (@Finset.univ A j).card
    exact congrArg Finset.card hu
  change (@Finset.univ A i).sum f / (↑(@Fintype.card A i) : ℝ) =
    (@Finset.univ A j).sum f / (↑(@Fintype.card A j) : ℝ)
  rw [hs, hc]

private theorem uniformMean_lower_fintype_irrel {A : Type} {i : Fintype A}
    (j : Fintype A) (η : ℝ) (f : A → ℝ)
    (h : η ≤ @uniformMean A i f) : η ≤ @uniformMean A j f := by
  rw [← uniformMean_fintype_irrel i j f]
  exact h

private theorem uniformMean_true {A : Type} (i : Fintype A) (hne : Nonempty A) :
    @uniformMean A i (fun _ => indicator True) = 1 := by
  have hcpos : 0 < @Fintype.card A i := Fintype.card_pos_iff.mpr hne
  have hc : (↑(@Fintype.card A i) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcpos)
  have hsum : (@Finset.univ A i).sum (fun _ : A => indicator True) =
      (↑(@Fintype.card A i) : ℝ) := by
    simp [indicator]
  change (@Finset.univ A i).sum (fun _ : A => indicator True) /
      (↑(@Fintype.card A i) : ℝ) = 1
  rw [hsum]
  exact div_self hc

private structure FintypeWitness (A : Type) where
  inst : Fintype A

private theorem endpoint_mass_transport
    (n q M L U : ℕ) (η : ℝ) (hLU : L ≤ U) (hηone : η ≤ 1)
    {jM : FintypeWitness (EdgeTuple (Fin n) M)}
    {jU : FintypeWitness (EdgeTuple (Fin n) U)}
    (hlowCDF : η ≤ cappedCDF (V := Fin n) q M L)
    (hhighTail : η ≤ cappedTail (V := Fin n) q M U)
    (htrans : ∀ f : ℕ → ℝ,
      @uniformMean (EdgeTuple (Fin n) M) jM.inst (fun x => f (clippedLast q L U x)) =
        @uniformMean (EdgeTuple (Fin n) U) jU.inst (fun x => f (deletionY q L x)))
    (hsample : Nonempty (EdgeTuple (Fin n) M)) :
    (η ≤ @uniformMean (EdgeTuple (Fin n) U) jU.inst
      (fun x => indicator ((deletionY q L x : ℝ) = (L : ℝ)))) ∧
    (η ≤ @uniformMean (EdgeTuple (Fin n) U) jU.inst
      (fun x => indicator ((deletionY q L x : ℝ) = (U : ℝ)))) := by
  have hLowTransport := htrans (fun k : ℕ => indicator ((k : ℝ) = (L : ℝ)))
  have hHighTransport := htrans (fun k : ℕ => indicator ((k : ℝ) = (U : ℝ)))
  have hfull := uniformMean_true jM.inst hsample
  constructor
  · by_cases hgap : L < U
    · have hEvents :
          (fun x : EdgeTuple (Fin n) M =>
            (clippedLast q L U x : ℝ) = (L : ℝ)) =
            (fun x => cappedLast q x ≤ L) := by
        funext x
        apply propext
        rw [clippedLast]
        simpa only [Nat.cast_inj] using
          clippedLower_eq_iff L U (cappedLast q x) hgap
      have hIndicatorEvents :
          (fun x : EdgeTuple (Fin n) M => indicator (cappedLast q x ≤ L)) =
            (fun x => indicator ((clippedLast q L U x : ℝ) = (L : ℝ))) := by
        funext x
        rw [← congrFun hEvents x]
      have hboundI : η ≤ @uniformMean (EdgeTuple (Fin n) M)
          (quantileTupleFintype (V := Fin n) M)
          (fun x => indicator (cappedLast q x ≤ L)) := by
        have h := hlowCDF
        rw [cappedCDF] at h
        unfold uniformProb at h
        exact uniformMean_lower_fintype_irrel (quantileTupleFintype (V := Fin n) M)
          η _ h
      have hboundI' : η ≤ @uniformMean (EdgeTuple (Fin n) M)
          (quantileTupleFintype (V := Fin n) M)
          (fun x => indicator ((clippedLast q L U x : ℝ) = (L : ℝ))) := by
        rw [← hIndicatorEvents]
        exact hboundI
      have hinst :
          @uniformMean (EdgeTuple (Fin n) M) (quantileTupleFintype (V := Fin n) M)
            (fun x => indicator ((clippedLast q L U x : ℝ) = (L : ℝ))) =
          @uniformMean (EdgeTuple (Fin n) M) jM.inst
            (fun x => indicator ((clippedLast q L U x : ℝ) = (L : ℝ))) :=
        uniformMean_fintype_irrel (quantileTupleFintype (V := Fin n) M) jM.inst _
      calc
        η ≤ @uniformMean (EdgeTuple (Fin n) M) (quantileTupleFintype (V := Fin n) M)
            (fun x => indicator ((clippedLast q L U x : ℝ) = (L : ℝ))) := hboundI'
        _ = @uniformMean (EdgeTuple (Fin n) M) jM.inst
            (fun x => indicator ((clippedLast q L U x : ℝ) = (L : ℝ))) := hinst
        _ = @uniformMean (EdgeTuple (Fin n) U) jU.inst
            (fun x => indicator ((deletionY q L x : ℝ) = (L : ℝ))) := hLowTransport
    · have hLUeq : L = U := Nat.le_antisymm hLU (le_of_not_gt hgap)
      have hEvents :
          (fun x : EdgeTuple (Fin n) M =>
            (clippedLast q L U x : ℝ) = (L : ℝ)) = (fun _ => True) := by
        funext x
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          rw [clippedLast, hLUeq]
          simp
      have hclipFull : @uniformMean (EdgeTuple (Fin n) M) jM.inst
          (fun x => indicator ((clippedLast q L U x : ℝ) = (L : ℝ))) = 1 := by
        calc
          _ = @uniformMean (EdgeTuple (Fin n) M) jM.inst (fun _ => indicator True) :=
            congrArg (fun p : EdgeTuple (Fin n) M → Prop =>
              @uniformMean (EdgeTuple (Fin n) M) jM.inst (fun x => indicator (p x))) hEvents
          _ = 1 := hfull
      have hdeletionFull : @uniformMean (EdgeTuple (Fin n) U) jU.inst
          (fun x => indicator ((deletionY q L x : ℝ) = (L : ℝ))) = 1 := by
        rw [← hLowTransport]
        exact hclipFull
      rw [hdeletionFull]
      exact hηone
  · by_cases hgap : L < U
    · have hEvents :
          (fun x : EdgeTuple (Fin n) M =>
            (clippedLast q L U x : ℝ) = (U : ℝ)) =
            (fun x => U ≤ cappedLast q x) := by
        funext x
        apply propext
        rw [clippedLast]
        simpa only [Nat.cast_inj] using
          clippedUpper_eq_iff L U (cappedLast q x) hgap
      have hIndicatorEvents :
          (fun x : EdgeTuple (Fin n) M => indicator (U ≤ cappedLast q x)) =
            (fun x => indicator ((clippedLast q L U x : ℝ) = (U : ℝ))) := by
        funext x
        rw [← congrFun hEvents x]
      have hboundI : η ≤ @uniformMean (EdgeTuple (Fin n) M)
          (quantileTupleFintype (V := Fin n) M)
          (fun x => indicator (U ≤ cappedLast q x)) := by
        have h := hhighTail
        rw [cappedTail] at h
        unfold uniformProb at h
        exact uniformMean_lower_fintype_irrel (quantileTupleFintype (V := Fin n) M)
          η _ h
      have hboundI' : η ≤ @uniformMean (EdgeTuple (Fin n) M)
          (quantileTupleFintype (V := Fin n) M)
          (fun x => indicator ((clippedLast q L U x : ℝ) = (U : ℝ))) := by
        rw [← hIndicatorEvents]
        exact hboundI
      have hinst :
          @uniformMean (EdgeTuple (Fin n) M) (quantileTupleFintype (V := Fin n) M)
            (fun x => indicator ((clippedLast q L U x : ℝ) = (U : ℝ))) =
          @uniformMean (EdgeTuple (Fin n) M) jM.inst
            (fun x => indicator ((clippedLast q L U x : ℝ) = (U : ℝ))) :=
        uniformMean_fintype_irrel (quantileTupleFintype (V := Fin n) M) jM.inst _
      calc
        η ≤ @uniformMean (EdgeTuple (Fin n) M) (quantileTupleFintype (V := Fin n) M)
            (fun x => indicator ((clippedLast q L U x : ℝ) = (U : ℝ))) := hboundI'
        _ = @uniformMean (EdgeTuple (Fin n) M) jM.inst
            (fun x => indicator ((clippedLast q L U x : ℝ) = (U : ℝ))) := hinst
        _ = @uniformMean (EdgeTuple (Fin n) U) jU.inst
            (fun x => indicator ((deletionY q L x : ℝ) = (U : ℝ))) := hHighTransport
    · have hLUeq : L = U := Nat.le_antisymm hLU (le_of_not_gt hgap)
      have hEvents :
          (fun x : EdgeTuple (Fin n) M =>
            (clippedLast q L U x : ℝ) = (U : ℝ)) = (fun _ => True) := by
        funext x
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          rw [clippedLast, hLUeq]
          simp
      have hclipFull : @uniformMean (EdgeTuple (Fin n) M) jM.inst
          (fun x => indicator ((clippedLast q L U x : ℝ) = (U : ℝ))) = 1 := by
        calc
          _ = @uniformMean (EdgeTuple (Fin n) M) jM.inst (fun _ => indicator True) :=
            congrArg (fun p : EdgeTuple (Fin n) M → Prop =>
              @uniformMean (EdgeTuple (Fin n) M) jM.inst (fun x => indicator (p x))) hEvents
          _ = 1 := hfull
      have hdeletionFull : @uniformMean (EdgeTuple (Fin n) U) jU.inst
          (fun x => indicator ((deletionY q L x : ℝ) = (U : ℝ))) = 1 := by
        rw [← hHighTransport]
        exact hclipFull
      rw [hdeletionFull]
      exact hηone

private theorem edgeTuple_nonempty (n M : ℕ) (hn : 2 ≤ n) :
    Nonempty (EdgeTuple (Fin n) M) := by
  let v₀ : Fin n := ⟨0, by omega⟩
  let v₁ : Fin n := ⟨1, by omega⟩
  have hp : Nonempty (Pair (Fin n)) := by
    refine ⟨⟨s(v₀, v₁), ?_⟩⟩
    intro v hv
    have hd : Sym2.IsDiag (s(v₀, v₁)) := by
      rw [hv]
      exact Sym2.mk_isDiag_iff.mpr rfl
    have h01 : v₀ = v₁ := Sym2.mk_isDiag_iff.mp hd
    have h01val := congrArg Fin.val h01
    dsimp [v₀, v₁] at h01val
    omega
  exact ⟨fun _ => Classical.choice hp⟩

theorem S4_RED_13AStatement_of_deps
    (h01C : S4_RED_01CStatement)
    (hpar : S4_PAR_01AStatement)
    (hqnt : PreQuantileStatement) :
    S4_RED_13AStatement := by
  intro q hq Λ hΛ n hn η hη hη0
  let M := cap Λ n
  let L := lowerLocation q Λ η n
  let U := upperLocation q Λ η n
  have hparΛ := (hpar q hq).2.2.2 Λ hΛ
  have hηzhalf : etaZero Λ < 1/2 := hparΛ.2.2.1
  have hηhalf : η ≤ 1/2 := le_of_lt (lt_of_le_of_lt hη0 hηzhalf)
  have hηone : η ≤ 1 := by linarith
  have hn2 : 2 ≤ n := by omega
  have hquant :
      L ≤ U ∧ U ≤ M ∧ η ≤ cappedCDF (V := Fin n) q M L ∧
        η ≤ cappedTail (V := Fin n) q M U ∧
        (∀ m : ℕ, m ≤ M → cappedTail (V := Fin n) q M m =
          processSurvival (V := Fin n) q m) ∧
        (∀ m : ℕ, m < M → cappedCDF (V := Fin n) q M m =
          1 - processSurvival (V := Fin n) q (m+1)) ∧
        (∀ m : ℕ, m ≤ L → 1 - η < processSurvival (V := Fin n) q m) ∧
        (∀ m : ℕ, U < m → m ≤ M → processSurvival (V := Fin n) q m < η) := by
    simpa [M, L, U, lowerLocation, upperLocation] using
      hqnt q n (cap Λ n) hq hn2 η hη hηhalf
  have hLU : L ≤ U := hquant.1
  have hUM : U ≤ M := hquant.2.1
  have hlowCDF : η ≤ cappedCDF (V := Fin n) q M L := hquant.2.2.1
  have hhighTail : η ≤ cappedTail (V := Fin n) q M U := hquant.2.2.2.1
  have hmass := endpoint_mass_transport n q M L U η hLU hηone
    hlowCDF hhighTail
    (h01C q n hq hn (cap Λ n) L U hLU hUM).1
    (edgeTuple_nonempty n M hn2)
  refine ⟨hLU, hUM, ?_, ?_⟩
  · simpa [uniformProb] using hmass.1
  · simpa [uniformProb] using hmass.2

end ThLean.W.S438

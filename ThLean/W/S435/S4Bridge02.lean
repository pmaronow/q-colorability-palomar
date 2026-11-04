module

public import ThLean.BP.S4.Bridges

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S435
open ThresholdFoundations
open ThLean.BP.S4

private lemma uniformProb_nonneg {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProb P := by
  unfold uniformProb uniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro x hx
    by_cases h : P x <;> simp [indicator, h]
  · exact Nat.cast_nonneg _

private lemma centeredWindow_bound (m : ℤ) (a : ℝ) (_ha : 0 ≤ a) (k : ℕ)
    (hc : |((k + 1 : ℕ) : ℝ) - (m : ℝ)| ≤ a) :
    k < Nat.floor ((m : ℝ) + a) := by
  have hbounds := abs_le.mp hc
  have hx : ((k + 1 : ℕ) : ℝ) ≤ (m : ℝ) + a := by linarith
  have hf : k + 1 ≤ Nat.floor ((m : ℝ) + a) := Nat.le_floor hx
  omega

private lemma sum_processSurvival_diff_Ico {V : Type*} [Fintype V] (q L U : ℕ)
    (hLU : L ≤ U) :
    (∑ k ∈ Finset.Ico L U,
      (processSurvival (V := V) q k - processSurvival (V := V) q (k + 1))) =
      processSurvival (V := V) q L - processSurvival (V := V) q U := by
  induction U generalizing L with
  | zero =>
      have hL : L = 0 := by omega
      subst L
      simp
  | succ U ih =>
      by_cases h : L ≤ U
      · rw [Finset.sum_Ico_succ_top h]
        rw [ih L h]
        ring
      · have hL : L = U + 1 := by omega
        subst L
        simp

theorem S4_BRIDGE_02Statement_of_deps
    (hA : ThLean.BP.S4.S4_BRIDGE_01AStatement) :
    ThLean.BP.S4.S4_BRIDGE_02Statement := by
  intro q n hq hn m a ha
  have hmass_nonneg (k : ℕ) : 0 ≤ hittingMass (V := Fin n) q k := by
    have hId := hA q n hq hn k (k + 1) (by omega)
    have hprob := uniformProb_nonneg
      (fun x : EdgeTuple (Fin n) (k + 1) =>
        k < boundedFailure q x ∧ boundedFailure q x ≤ k + 1)
    have hterm_nonneg : 0 ≤ terminalProb (V := Fin n) q k (k + 1) (fun _ _ => True) := by
      rw [hId.2 (k + 1) (by omega)]
      exact hprob
    rw [hId.1] at hterm_nonneg
    simpa [hittingMass] using hterm_nonneg
  have hwindow_eq :
      hittingWindowProbability (V := Fin n) q m a =
        ∑' k : ℕ, hittingMass (V := Fin n) q k *
          indicator (|((k + 1 : ℕ) : ℝ) - (m : ℝ)| ≤ a) := by
    let B := Nat.floor ((m : ℝ) + a)
    let f : ℕ → ℝ := fun k => hittingMass (V := Fin n) q k *
      indicator (|((k + 1 : ℕ) : ℝ) - (m : ℝ)| ≤ a)
    have hsub : {k : ℕ | f k ≠ 0} ⊆ Finset.range B := by
      intro k hk
      have hparts :
          |((k + 1 : ℕ) : ℝ) - (m : ℝ)| ≤ a ∧ hittingMass (V := Fin n) q k ≠ 0 := by
        simpa [f, indicator] using hk
      have hc := hparts.1
      exact Finset.mem_range.mpr (centeredWindow_bound m a ha k hc)
    have hzero : ∀ k : ℕ, k ∉ Finset.range B → f k = 0 := by
      intro k hk
      by_contra hne
      have hmem : k ∈ {k : ℕ | f k ≠ 0} := hne
      exact hk (hsub hmem)
    calc
      hittingWindowProbability (V := Fin n) q m a =
          ∑ k ∈ Finset.range B, if |((k + 1 : ℕ) : ℝ) - (m : ℝ)| ≤ a
            then hittingMass (V := Fin n) q k else 0 := by
        rfl
      _ = ∑ k ∈ Finset.range B, f k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [f, indicator]
      _ = ∑' k : ℕ, f k := (tsum_eq_sum (s := Finset.range B) hzero).symm
      _ = ∑' k : ℕ, hittingMass (V := Fin n) q k *
          indicator (|((k + 1 : ℕ) : ℝ) - (m : ℝ)| ≤ a) := by
        rfl
  have hwindow_finite : Set.Finite {k : ℕ | hittingMass (V := Fin n) q k *
      indicator (|((k + 1 : ℕ) : ℝ) - (m : ℝ)| ≤ a) ≠ 0} := by
    let B := Nat.floor ((m : ℝ) + a)
    have hsub : {k : ℕ | hittingMass (V := Fin n) q k *
        indicator (|((k + 1 : ℕ) : ℝ) - (m : ℝ)| ≤ a) ≠ 0} ⊆ Finset.range B := by
      intro k hk
      have hparts :
          |((k + 1 : ℕ) : ℝ) - (m : ℝ)| ≤ a ∧ hittingMass (V := Fin n) q k ≠ 0 := by
        simpa [indicator] using hk
      have hc := hparts.1
      exact Finset.mem_range.mpr (centeredWindow_bound m a ha k hc)
    exact (Finset.finite_toSet (Finset.range B)).subset hsub
  refine ⟨hwindow_eq, hwindow_finite, ?_⟩
  intro L U hLU hm hwidth
  subst m
  let I := Finset.Ico L (U + 1)
  let B := Nat.floor ((L : ℝ) + a)
  let R := Finset.range B
  have htel := sum_processSurvival_diff_Ico (V := Fin n) q L (U + 1) (by omega)
  have hterm_eq :
      terminalProb (V := Fin n) q L (U + 1) (fun _ _ => True) =
        ∑ k ∈ I, hittingMass (V := Fin n) q k := by
    calc
      terminalProb (V := Fin n) q L (U + 1) (fun _ _ => True) =
          processSurvival (V := Fin n) q L -
            processSurvival (V := Fin n) q (U + 1) :=
        (hA q n hq hn L (U + 1) (by omega)).1
      _ = ∑ k ∈ I, hittingMass (V := Fin n) q k := by
        simpa [hittingMass] using htel.symm
  have hI_sub_R : I ⊆ R := by
    intro k hk
    have hkI : L ≤ k ∧ k < U + 1 := Finset.mem_Ico.mp hk
    have hkn : k + 1 ≤ U + 1 := by omega
    have hcast : ((k + 1 : ℕ) : ℝ) ≤ (U : ℝ) + 1 := by
      exact_mod_cast hkn
    have hfloor : k + 1 ≤ B := by
      apply Nat.le_floor
      linarith
    exact Finset.mem_range.mpr (by omega)
  have hcond_on_I (k : ℕ) (hk : k ∈ I) :
      |((k + 1 : ℕ) : ℝ) - (L : ℝ)| ≤ a := by
    have hkI : L ≤ k ∧ k < U + 1 := Finset.mem_Ico.mp hk
    have hkn : k + 1 ≤ U + 1 := by omega
    have hcast : ((k + 1 : ℕ) : ℝ) ≤ (U : ℝ) + 1 := by
      exact_mod_cast hkn
    have hLreal : (L : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkI.1
    have hkreal : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ k)
    have hnonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) - (L : ℝ) := by linarith
    have hupper : ((k + 1 : ℕ) : ℝ) - (L : ℝ) ≤ a := by
      linarith [hwidth]
    exact abs_le.mpr ⟨by linarith, hupper⟩
  have hcond_on_I' (k : ℕ) (hk : k ∈ I) :
      |(k : ℝ) + 1 - (L : ℝ)| ≤ a := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcond_on_I k hk
  have hsum_le :
      (∑ k ∈ I, hittingMass (V := Fin n) q k) ≤
        ∑ k ∈ R, hittingMass (V := Fin n) q k *
          indicator (|((k + 1 : ℕ) : ℝ) - (L : ℝ)| ≤ a) := by
    calc
      (∑ k ∈ I, hittingMass (V := Fin n) q k) =
          ∑ k ∈ R, if k ∈ I then hittingMass (V := Fin n) q k else 0 := by
        calc
          (∑ k ∈ I, hittingMass (V := Fin n) q k) =
              ∑ k ∈ I, if k ∈ I then hittingMass (V := Fin n) q k else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [hk]
          _ = ∑ k ∈ R, if k ∈ I then hittingMass (V := Fin n) q k else 0 := by
            apply Finset.sum_subset hI_sub_R
            intro k hkR hkI
            simp [hkI]
      _ ≤ ∑ k ∈ R, hittingMass (V := Fin n) q k *
          indicator (|((k + 1 : ℕ) : ℝ) - (L : ℝ)| ≤ a) := by
        apply Finset.sum_le_sum
        intro k hkR
        by_cases hkI : k ∈ I
        · have hc := hcond_on_I' k hkI
          simp [indicator, hkI, hc]
        · by_cases hc : |((k + 1 : ℕ) : ℝ) - (L : ℝ)| ≤ a
          · have hc' : |(k : ℝ) + 1 - (L : ℝ)| ≤ a := by
              simpa only [Nat.cast_add, Nat.cast_one] using hc
            simpa [indicator, hkI, hc'] using hmass_nonneg k
          · have hc' : ¬ |(k : ℝ) + 1 - (L : ℝ)| ≤ a := by
              simpa only [Nat.cast_add, Nat.cast_one] using hc
            simp [indicator, hkI, hc']
  calc
    terminalProb (V := Fin n) q L (U + 1) (fun _ _ => True) =
        ∑ k ∈ I, hittingMass (V := Fin n) q k := hterm_eq
    _ ≤ ∑ k ∈ R, hittingMass (V := Fin n) q k *
        indicator (|((k + 1 : ℕ) : ℝ) - (L : ℝ)| ≤ a) := hsum_le
    _ = hittingWindowProbability (V := Fin n) q (L : ℤ) a := by
      symm
      calc
        hittingWindowProbability (V := Fin n) q (L : ℤ) a =
            ∑' k : ℕ, hittingMass (V := Fin n) q k *
              indicator (|((k + 1 : ℕ) : ℝ) - ((L : ℤ) : ℝ)| ≤ a) := hwindow_eq
        _ = ∑ k ∈ R, hittingMass (V := Fin n) q k *
              indicator (|((k + 1 : ℕ) : ℝ) - (L : ℝ)| ≤ a) := by
          apply tsum_eq_sum
          intro k hk
          by_contra hne
          have hparts :
              |((k + 1 : ℕ) : ℝ) - (L : ℝ)| ≤ a ∧ hittingMass (V := Fin n) q k ≠ 0 := by
            simpa [indicator] using hne
          have hlt := centeredWindow_bound (L : ℤ) a ha k (by simpa using hparts.1)
          exact hk (Finset.mem_range.mpr hlt)

end ThLean.W.S435

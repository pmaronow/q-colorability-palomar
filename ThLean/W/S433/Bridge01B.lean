module

public import ThLean.BP.S4.Bridges

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S433
open ThresholdFoundations
open ThLean.BP.S4

@[instance_reducible]
local instance (priority := 2000) canonicalPairFintypeInst (n : ℕ) :
    Fintype (Pair (Fin n)) := by
  classical
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  letI : DecidableEq (Sym2 (Fin n)) := Sym2.instDecidableEq
  letI : Fintype (Sym2 (Fin n)) := Sym2.instFintype
  letI : DecidablePred (fun e : Sym2 (Fin n) => ∀ v : Fin n, e ≠ s(v, v)) :=
    fun e => Fintype.decidableForallFintype
  exact @Subtype.fintype (Sym2 (Fin n))
    (fun e => ∀ v : Fin n, e ≠ s(v, v)) inferInstance inferInstance

private lemma finPair_nonempty {n : ℕ} (hn : 2 ≤ n) : Nonempty (Pair (Fin n)) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [a, b] at hval
    omega
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hv
  rcases (Sym2.eq_iff).mp hv with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hab (ha.trans hb.symm)
  · exact hab (ha.trans hb.symm)

private lemma terminalStepENN_finite {n q m : ℕ} (P : MGraph (Fin n) → Pair (Fin n) → Prop)
    [Nonempty (Pair (Fin n))] [Fintype (Pair (Fin n))] :
    terminalStepENN q m (fun G e => if P G e then 1 else 0) ≠ ∞ := by
  unfold terminalStepENN uniformMeanENN
  apply ENNReal.div_ne_top
  · apply ENNReal.sum_ne_top.2
    intro x hx
    apply ENNReal.div_ne_top
    · apply ENNReal.sum_ne_top.2
      intro e he
      by_cases hc : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
      · by_cases hp : P (tupleGraph x) e <;> simp [hc, hp]
      · simp [hc]
    · simp
  · simp

private lemma ennreal_toReal_univ_sum {α : Type*} [Fintype α]
    (f : α → ℝ≥0∞) (hf : ∀ a, f a ≠ ∞) :
    (∑ a, f a).toReal = ∑ a, (f a).toReal := by
  simpa using (ENNReal.toReal_sum (s := Finset.univ) (f := f) (by
    intro a ha
    exact hf a))

private lemma terminalStepENN_toReal {n q m : ℕ} (P : MGraph (Fin n) → Pair (Fin n) → Prop)
    [Nonempty (Pair (Fin n))] :
    (terminalStepENN q m (fun G e => if P G e then 1 else 0)).toReal =
      uniformMean (fun x : EdgeTuple (Fin n) m =>
        uniformMean (fun e : Pair (Fin n) =>
          if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
          then indicator (P (tupleGraph x) e) else 0)) := by
  classical
  unfold terminalStepENN uniformMeanENN
  dsimp
  rw [ENNReal.toReal_div]
  have hfinite : ∀ x : EdgeTuple (Fin n) m,
      (∑ e : Pair (Fin n),
        if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
        then if P (tupleGraph x) e then 1 else 0 else 0) /
        (Fintype.card (Pair (Fin n)) : ℝ≥0∞) ≠ ∞ := by
    intro x
    apply ENNReal.div_ne_top
    · apply ENNReal.sum_ne_top.2
      intro e he
      by_cases hc : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
      · by_cases hp : P (tupleGraph x) e <;> simp [hc, hp]
      · simp [hc]
    · simp
  rw [ennreal_toReal_univ_sum _ hfinite]
  unfold uniformMean
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [ENNReal.toReal_div]
  rw [ennreal_toReal_univ_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro e he
    by_cases hc : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
    · by_cases hp : P (tupleGraph x) e <;> simp [hc, hp, indicator]
    · simp [hc]
  · intro e he
    by_cases hc : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
    · by_cases hp : P (tupleGraph x) e
      · simp [hc, hp] at he
      · simp [hc, hp] at he
    · simp [hc] at he

private lemma terminalProb_eq_sum_step_toReal {n q L U : ℕ}
    (P : MGraph (Fin n) → Pair (Fin n) → Prop) [Nonempty (Pair (Fin n))] :
    terminalProb q L U P =
      ∑ m ∈ Finset.Ico L U,
        (terminalStepENN q m (fun G e => if P G e then 1 else 0)).toReal := by
  unfold terminalProb terminalReal
  apply Finset.sum_congr rfl
  intro m hm
  exact (terminalStepENN_toReal P).symm

private lemma terminalStepENN_event_le {n q m : ℕ}
    (P : MGraph (Fin n) → Pair (Fin n) → Prop) :
    terminalStepENN q m (fun G e => if P G e then 1 else 0) ≤
      terminalStepENN q m (fun _ : MGraph (Fin n) => fun _ : Pair (Fin n) => (1 : ℝ≥0∞)) := by
  unfold terminalStepENN uniformMeanENN
  apply ENNReal.div_le_div_right
  apply Finset.sum_le_sum
  intro x hx
  apply ENNReal.div_le_div_right
  apply Finset.sum_le_sum
  intro e he
  by_cases hc : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
  · by_cases hp : P (tupleGraph x) e <;> simp [hc, hp]
  · simp [hc]

theorem S4_BRIDGE_01BStatement_of_deps
    (hA : S4_BRIDGE_01AStatement) (hLife : PreLifetimeStatement.{0}) :
    S4_BRIDGE_01BStatement := by
  intro q n hq hn
  have hPairNonempty : Nonempty (Pair (Fin n)) := finPair_nonempty (by omega)
  letI : Nonempty (Pair (Fin n)) := hPairNonempty
  let a : ℕ → ℝ≥0∞ := fun m =>
    terminalStepENN q m (fun _ : MGraph (Fin n) => fun _ : Pair (Fin n) => (1 : ℝ≥0∞))
  have hzero : Loopless (0 : MGraph (Fin n)) := by
    intro v
    rfl
  have hLife0 := (hLife (Fin n) q hq (by
    have hn' : 2 ≤ n := by omega
    simpa using hn')).1 (0 : MGraph (Fin n)) hzero
  rcases hLife0 with ⟨_, _, _, _, hLifeSize⟩
  have hLifeSize := hLifeSize (by simpa using hn)
  rcases hLifeSize with ⟨_, _, hSurvSummable, _⟩
  have hSurvZero : Tendsto
      (fun N : ℕ => processSurvival (V := Fin n) q N) atTop (𝓝 0) := by
    simpa [processSurvival] using hSurvSummable.tendsto_atTop_zero
  have hRealLimit : Tendsto
      (fun N : ℕ => 1 - processSurvival (V := Fin n) q N) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hSurvZero
  have hENNLimit : Tendsto
      (fun N : ℕ => ENNReal.ofReal (1 - processSurvival (V := Fin n) q N)) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal hRealLimit
  have hPartialReal : ∀ N : ℕ,
      (∑ m ∈ Finset.range N, (a m).toReal) =
        terminalProb q 0 N
          (fun _ : MGraph (Fin n) => fun _ : Pair (Fin n) => True) := by
    intro N
    have h := terminalProb_eq_sum_step_toReal (n := n) (q := q) (L := 0) (U := N)
      (P := fun _ : MGraph (Fin n) => fun _ : Pair (Fin n) => True)
    simpa [a, Nat.Ico_zero_eq_range] using h.symm
  have hPartialFinite : ∀ N : ℕ,
      (∑ m ∈ Finset.range N, a m) ≠ ∞ := by
    intro N
    apply ENNReal.sum_ne_top.2
    intro m hm
    simpa [a] using
      (terminalStepENN_finite (n := n) (q := q) (m := m)
        (P := fun _ : MGraph (Fin n) => fun _ : Pair (Fin n) => True))
  have hPartialEq : ∀ N : ℕ,
      (∑ m ∈ Finset.range N, a m) =
        ENNReal.ofReal (1 - processSurvival (V := Fin n) q N) := by
    intro N
    rw [← ENNReal.ofReal_toReal (hPartialFinite N)]
    apply congrArg ENNReal.ofReal
    calc
      (∑ m ∈ Finset.range N, a m).toReal =
          ∑ m ∈ Finset.range N, (a m).toReal := by
            rw [ENNReal.toReal_sum (fun m hm => by
              have h := terminalStepENN_finite (n := n) (q := q) (m := m)
                (P := fun _ : MGraph (Fin n) => fun _ : Pair (Fin n) => True)
              simpa [a] using h)]
      _ = terminalProb q 0 N (fun _ _ => True) := hPartialReal N
      _ = processSurvival (V := Fin n) q 0 - processSurvival (V := Fin n) q N :=
        (hA q n hq hn 0 N (Nat.zero_le N)).1
      _ = 1 - processSurvival (V := Fin n) q N := by
        rw [ThresholdFoundations.Sanity.processSurvival_zero (by omega)]
  have hTotal : (∑' m : ℕ, a m) = 1 := by
    have hTsum := ENNReal.tendsto_nat_tsum a
    have hPartialLimit : Tendsto
        (fun N : ℕ => ∑ m ∈ Finset.range N, a m) atTop (𝓝 1) := by
      have heq : (fun N : ℕ => ∑ m ∈ Finset.range N, a m) =
          fun N => ENNReal.ofReal (1 - processSurvival (V := Fin n) q N) := by
        funext N
        exact hPartialEq N
      rw [heq]
      exact hENNLimit
    exact tendsto_nhds_unique hTsum hPartialLimit
  constructor
  · have h := congrArg ENNReal.toReal hTotal
    simpa [terminalProbability, terminalMeanENN, a] using h
  · intro L U hLU P
    let b : ℕ → ℝ≥0∞ := fun m =>
      terminalStepENN q m (fun G e => if P G e then 1 else 0)
    have hTerms : ∀ m, b m ≤ a m := by
      intro m
      simpa [a, b] using terminalStepENN_event_le (n := n) (q := q) (m := m) P
    have hTsumP : (∑' m : ℕ, b m) ≤ 1 := by
      calc
        (∑' m : ℕ, b m) ≤ ∑' m : ℕ, a m := ENNReal.tsum_le_tsum hTerms
        _ = 1 := hTotal
    have hTsumPFinite : (∑' m : ℕ, b m) ≠ ∞ := by
      apply ne_of_lt
      exact lt_of_le_of_lt hTsumP (by simp)
    have hFiniteLe : (∑ m ∈ Finset.Ico L U, b m) ≤ ∑' m : ℕ, b m :=
      ENNReal.sum_le_tsum _
    have hWindowRep := terminalProb_eq_sum_step_toReal
      (n := n) (q := q) (L := L) (U := U) (P := P)
    constructor
    · rw [hWindowRep]
      positivity
    · calc
        terminalProb q L U P =
            ∑ m ∈ Finset.Ico L U, (b m).toReal := hWindowRep
        _ = (∑ m ∈ Finset.Ico L U, b m).toReal := by
          symm
          rw [ENNReal.toReal_sum (fun m hm => by
            have ht := terminalStepENN_finite (n := n) (q := q) (m := m) P
            simpa [b] using ht)]
        _ ≤ (∑' m : ℕ, b m).toReal := ENNReal.toReal_mono hTsumPFinite hFiniteLe
        _ = terminalProbability q P := rfl

end ThLean.W.S433

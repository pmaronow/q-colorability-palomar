import ThLean.BP.S6.Potential

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S628

open ThLean.BP.S6

private lemma prefix_subgraph {n M : ℕ} (x : Hist n M) {a b : ℕ} (hab : a ≤ b) :
    subgraph (tuplePrefix x a) (tuplePrefix x b) := by
  intro e
  unfold tuplePrefix
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1.trans_le hab, hi.2⟩

private lemma colorable_prefix_mono {n M q : ℕ} (x : Hist n M) {a b : ℕ}
    (hab : a ≤ b) (hb : Colorable q (tuplePrefix x b)) :
    Colorable q (tuplePrefix x a) := by
  obtain ⟨σ, hσ⟩ := hb
  refine ⟨σ, ?_⟩
  intro u v huv
  apply hσ u v
  exact lt_of_lt_of_le huv (prefix_subgraph x hab (s(u, v)))

private lemma finiteHittingTime_le_of_bad {n M q : ℕ} (x : Hist n M) {i : ℕ}
    (hi : i ≤ M) (hbad : ¬ Colorable q (tuplePrefix x i)) :
    finiteHittingTime q x ≤ i := by
  unfold finiteHittingTime
  split_ifs with hex
  · exact Nat.find_min' hex ⟨hi, hbad⟩
  · exact (hex ⟨i, hi, hbad⟩).elim

private lemma finiteHittingTime_gt_of_colorable {n M q : ℕ} (x : Hist n M) {i : ℕ}
    (hi : i < M) (hcol : Colorable q (tuplePrefix x i)) :
    i < finiteHittingTime q x := by
  unfold finiteHittingTime
  split_ifs with hex
  · by_contra hnot
    have hfi : Nat.find hex ≤ i := Nat.le_of_not_gt hnot
    have hspec := Nat.find_spec hex
    exact hspec.2 (colorable_prefix_mono x hfi hcol)
  · omega

private lemma colorable_iff_before_stop {n M q : ℕ} (x : Hist n M) {i : ℕ}
    (hi : i < M) :
    Colorable q (tuplePrefix x i) ↔ i < finiteStoppedTime q x := by
  constructor
  · intro hcol
    unfold finiteStoppedTime
    exact lt_min (finiteHittingTime_gt_of_colorable x hi hcol) hi
  · intro h
    by_contra hcol
    have hbad := finiteHittingTime_le_of_bad x (Nat.le_of_lt hi) hcol
    unfold finiteStoppedTime at h
    omega

private lemma tuplePrefix_succ {n M : ℕ} (x : Hist n M) {i : ℕ} (hi : i < M) :
    tuplePrefix x (i + 1) = addPair (tuplePrefix x i) (x ⟨i, hi⟩) := by
  classical
  funext e
  let last : Fin M := ⟨i, hi⟩
  have hset :
      (Finset.univ.filter (fun j : Fin M => j.val ≤ i ∧ (x j).val = e)) =
        (if (x last).val = e then
          insert last (Finset.univ.filter (fun j : Fin M => j.val < i ∧ (x j).val = e))
        else Finset.univ.filter (fun j : Fin M => j.val < i ∧ (x j).val = e)) := by
    ext j
    by_cases hji : j.val = i
    · have hj : j = last := Fin.ext hji
      subst j
      by_cases hcurr : (x last).val = e <;> simp [hcurr, last]
    · have hval : j.val ≠ i := by
        exact hji
      have hje : j ≠ last := by
        intro heq
        exact hji (by simpa [last] using congrArg Fin.val heq)
      have hlt : j.val ≤ i ↔ j.val < i := by omega
      by_cases hcurr : (x last).val = e <;> simp [hcurr, hje, hval, hlt]
  have hleft :
      Finset.univ.filter (fun j : Fin M => j.val < i + 1 ∧ (x j).val = e) =
        Finset.univ.filter (fun j : Fin M => j.val ≤ i ∧ (x j).val = e) := by
    ext j
    simp [Nat.lt_succ_iff]
  have hlastnot : last ∉ Finset.univ.filter
      (fun j : Fin M => j.val < i ∧ (x j).val = e) := by
    simp [last]
  have hcard := congrArg Finset.card hset
  simp only [tuplePrefix, addPair, addEdge, Function.update]
  by_cases hcurr : (x last).val = e
  · rw [if_pos hcurr, Finset.card_insert_of_notMem hlastnot] at hcard
    have hcurr' : e = (x last).val := hcurr.symm
    simpa [hleft, last, eq_comm, hcurr'] using hcard
  · rw [if_neg hcurr] at hcard
    have hcurr' : e ≠ (x last).val := Ne.symm hcurr
    simpa [hleft, last, eq_comm, hcurr'] using hcard

private lemma sum_Ico_differences (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Finset.Ico a b, (f (i + 1) - f i)) = f b - f a := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      simp [ha]
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ico_succ_top hab']
        rw [ih hab']
        ring
      · have ha : a = b + 1 := by omega
        simp [ha]

private lemma sum_range_filter_eq_Ico {M a b : ℕ} (hab : a ≤ b) (hbM : b ≤ M)
    (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range M, if a ≤ i ∧ i < b then f i else 0) =
      ∑ i ∈ Finset.Ico a b, f i := by
  classical
  have hsubset : Finset.Ico a b ⊆ Finset.range M := by
    intro i hi
    simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
    omega
  calc
    (∑ i ∈ Finset.range M, if a ≤ i ∧ i < b then f i else 0) =
        ∑ i ∈ (Finset.range M).filter (fun i => a ≤ i ∧ i < b), f i := by
          simp [Finset.sum_filter]
    _ = ∑ i ∈ Finset.Ico a b, f i := by
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          omega

/-- Deterministic telescope derived from the one-step saturated-potential estimate. -/
theorem S6_27Statement_of_deps (h26 : S6_26Statement) : S6_27Statement := by
  intro n q M hn hq u x s
  let τ := finiteStoppedTime q x
  let inc : ℕ → ℝ := fun i =>
    if hi : i < M then creditIncrement q (tuplePrefix x i) u (x ⟨i, hi⟩) else 0
  by_cases hs : s < (τ : WithTop ℕ)
  · cases s with
    | top => simp at hs
    | coe a =>
      have haτ : a < τ := by simpa using hs
      have hτM : τ ≤ M := by
        dsimp [τ, finiteStoppedTime]
        exact Nat.min_le_right _ _
      let v₀ : Fin n := ⟨0, by omega⟩
      let v₁ : Fin n := ⟨1, by omega⟩
      have e₀ : Edge n := ⟨s(v₀, v₁), by simp [v₀, v₁]⟩
      have hpotential (i : ℕ) :
          ThLean.BP.S6.saturatedPotential q (tuplePrefix x i) u ≤ Real.log n := by
        exact (h26 n q hn hq (tuplePrefix x i) u e₀).2.1
      have hpotential_nonneg (i : ℕ) :
          0 ≤ ThLean.BP.S6.saturatedPotential q (tuplePrefix x i) u := by
        exact (h26 n q hn hq (tuplePrefix x i) u e₀).1
      have hterm (i : ℕ) (hi : i ∈ Finset.Ico a τ) :
          inc i ≤
            ThLean.BP.S6.saturatedPotential q (tuplePrefix x (i + 1)) u -
              ThLean.BP.S6.saturatedPotential q (tuplePrefix x i) u := by
        have hi' := Finset.mem_Ico.mp hi
        have hiM : i < M := by omega
        have hstep := (h26 n q hn hq (tuplePrefix x i) u (x ⟨i, hiM⟩)).2.2.2.1
        rw [← tuplePrefix_succ x hiM] at hstep
        simpa [inc, hiM] using hstep
      have hsum : (∑ i ∈ Finset.Ico a τ, inc i) ≤
            ThLean.BP.S6.saturatedPotential q (tuplePrefix x τ) u -
              ThLean.BP.S6.saturatedPotential q (tuplePrefix x a) u := by
        calc
          _ ≤ ∑ i ∈ Finset.Ico a τ,
              (ThLean.BP.S6.saturatedPotential q (tuplePrefix x (i + 1)) u -
                ThLean.BP.S6.saturatedPotential q (tuplePrefix x i) u) := by
                  apply Finset.sum_le_sum
                  intro i hi
                  exact hterm i hi
          _ = ThLean.BP.S6.saturatedPotential q (tuplePrefix x τ) u -
                ThLean.BP.S6.saturatedPotential q (tuplePrefix x a) u :=
                  sum_Ico_differences
                    (fun i => ThLean.BP.S6.saturatedPotential q (tuplePrefix x i) u)
                    (Nat.le_of_lt haτ)
      have hcredit_eq : suffixCredits q u (a : WithTop ℕ) x =
          ∑ i ∈ Finset.Ico a τ, inc i := by
        have hcond (i : ℕ) (hi : i < M) :
            ((a : WithTop ℕ) ≤ (i : WithTop ℕ) ∧ Colorable q (tuplePrefix x i)) ↔
              a ≤ i ∧ i < τ := by
          constructor
          · rintro ⟨hsi, hcol⟩
            exact ⟨WithTop.coe_le_coe.mp hsi,
              by simpa [τ] using (colorable_iff_before_stop x hi).mp hcol⟩
          · rintro ⟨hai, hit⟩
            refine ⟨WithTop.coe_le_coe.mpr hai, ?_⟩
            exact (colorable_iff_before_stop x hi).mpr (by simpa [τ] using hit)
        let f : ℕ → ℝ := fun i =>
          if hi : i < M then
            if (a : WithTop ℕ) ≤ (i : WithTop ℕ) ∧ Colorable q (tuplePrefix x i)
            then creditIncrement q (tuplePrefix x i) u (x ⟨i, hi⟩) else 0
          else 0
        have hfin : suffixCredits q u (a : WithTop ℕ) x = ∑ i : Fin M, f i.val := by
          unfold suffixCredits
          apply Finset.sum_congr rfl
          intro i _
          simp [f, i.isLt]
        rw [hfin, Fin.sum_univ_eq_sum_range f M]
        calc
          (∑ i ∈ Finset.range M, f i) =
              ∑ i ∈ Finset.range M,
                if a ≤ i ∧ i < τ then inc i else 0 := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    have hiM : i < M := Finset.mem_range.mp hi
                    by_cases hc : a ≤ i ∧ i < τ
                    · have hc' := (hcond i hiM).mpr hc
                      simp [f, hc, hc', inc, hiM]
                    · have hc' := fun hh => hc ((hcond i hiM).mp hh)
                      have hfalse : ¬ ((a : WithTop ℕ) ≤ (i : WithTop ℕ) ∧
                          Colorable q (tuplePrefix x i)) := hc'
                      simp only [f, dif_pos hiM]
                      rw [if_neg hfalse, if_neg hc]
          _ = ∑ i ∈ Finset.Ico a τ, inc i :=
                sum_range_filter_eq_Ico (Nat.le_of_lt haτ) hτM inc
      have hbound : suffixCredits q u (a : WithTop ℕ) x ≤ Real.log n := by
        rw [hcredit_eq]
        calc
          _ ≤ ThLean.BP.S6.saturatedPotential q (tuplePrefix x τ) u -
                ThLean.BP.S6.saturatedPotential q (tuplePrefix x a) u := hsum
          _ ≤ Real.log n := by linarith [hpotential τ, hpotential_nonneg a]
      have hs' : (a : WithTop ℕ) < (finiteStop q x : WithTop ℕ) := by
        simpa [τ, finiteStop] using hs
      simpa [indicator, hs'] using hbound
  · have hzero : suffixCredits q u s x = 0 := by
      unfold suffixCredits
      apply Finset.sum_eq_zero
      intro i hi
      split_ifs with hc
      · have hidx := hc.1
        have hcol := hc.2
        have hiM : i.val < M := i.isLt
        have hbefore := (colorable_iff_before_stop x hiM).1 hcol
        have hsi : s ≤ (i.val : WithTop ℕ) := hidx
        have hitau : (i.val : WithTop ℕ) < (τ : WithTop ℕ) := by
          simpa [τ] using hbefore
        exact (hs (hsi.trans_lt hitau)).elim
      · rfl
    rw [hzero]
    have hs' : ¬ s < (finiteStop q x : WithTop ℕ) := by
      simpa [τ, finiteStop] using hs
    simp [indicator, hs']

end ThLean.W.S628

end

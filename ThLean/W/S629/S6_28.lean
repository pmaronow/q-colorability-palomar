import ThLean.BP.S6.Potential

noncomputable section
open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S629

private theorem uniformMean_sum_range {A : Type*} [Fintype A] (M : ℕ)
    (f : ℕ → A → ℝ) :
    uniformMean (fun x => ∑ m ∈ Finset.range M, f m x) =
      ∑ m ∈ Finset.range M, uniformMean (f m) := by
  unfold uniformMean
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_div]

private theorem uniformMean_sum_fin {A : Type*} [Fintype A] (M : ℕ)
    (f : Fin M → A → ℝ) :
    uniformMean (fun x => ∑ i : Fin M, f i x) =
      ∑ i : Fin M, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_div]

private def padHist {n m M : ℕ} (e₀ : Edge n)
    (x : Hist n m) : Hist n M := fun i =>
  if hi : i.val < m then x ⟨i.val, hi⟩ else e₀

private theorem padHist_eq {n m M : ℕ} (e₀ : Edge n) (hm : m ≤ M)
    (x : Hist n M) (i : Fin M) (hi : i.val < m) :
    padHist e₀ (takePrefix hm x) i = x i := by
  simp [padHist, takePrefix, hi]

private def prefixGraph {n m M : ℕ} (e₀ : Edge n) (x : Hist n m) : Graph n :=
  tuplePrefix (M := M) (padHist (M := M) e₀ x) m

private theorem tuplePrefix_factor {n m M : ℕ} (e₀ : Edge n) (hm : m ≤ M)
    (x : Hist n M) : tuplePrefix x m = prefixGraph (M := M) e₀ (takePrefix hm x) := by
  funext e
  unfold prefixGraph
  simp only [tuplePrefix]
  apply Finset.card_bij (fun i _ => i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with ⟨him, hxe⟩
    refine ⟨him, ?_⟩
    rw [padHist_eq e₀ hm x i him]
    exact hxe
  · intro a ha b hb hab
    exact hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨b, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hb.1, ?_⟩
    rw [← padHist_eq e₀ hm x b hb.1]
    exact hb.2

private theorem uniformMean_mono {A : Type} [Fintype A]
    (hmean : MeanRules A) {f g : A → ℝ} (hfg : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g := hmean.mono f g hfg

/-- Finite predictable averaging, using exactly the preceding S6 leaf statements. -/
theorem S6_28Statement_of_deps
    (h01a : ThLean.BP.S6.S6_01aStatement)
    (h01b : ThLean.BP.S6.S6_01bStatement)
    (h05 : ThLean.BP.S6.S6_05Statement)
    (h23 : ThLean.BP.S6.S6_23Statement)
    (h24b : ThLean.BP.S6.S6_24bStatement)
    (h27 : ThLean.BP.S6.S6_27Statement) :
    ThLean.BP.S6.S6_28Statement := by
  intro n q M hn hq u T hT
  classical
  have h01aHist := h01a (Hist n M)
  have h01bHist := h01b n hn
  have h25 := ThLean.BP.S6.S6_25_assembly h01a h05 h23 h24b
  have hcoef : 0 ≤ (2 / Real.log 2 : ℝ) := by
    exact le_of_lt (div_pos (by norm_num) h23.1)
  have hnEdges : 1 < n := by omega
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let e₀ : Edge n := ⟨s(a, b), by
    intro v hv
    have heq := (Sym2.eq_iff.mp hv)
    have hab : a = b := by
      rcases heq with ⟨hav, hbv⟩ | ⟨hav, hbv⟩
      · exact hav.trans hbv.symm
      · exact hav.trans hbv.symm
    have h01 : (0 : ℕ) = 1 := by simpa [a, b] using congrArg Fin.val hab
    omega⟩
  let c : ℝ := 2 / Real.log 2
  have hterm : ∀ i : Fin M,
      uniformMean (fun x : Hist n M =>
        if T x ≤ (i.val : WithTop ℕ) ∧ Colorable q (tuplePrefix x i.val)
        then beta q (tuplePrefix x i.val) u else 0) ≤
      c * uniformMean (fun x : Hist n M =>
        if T x ≤ (i.val : WithTop ℕ) ∧ Colorable q (tuplePrefix x i.val)
        then creditIncrement q (tuplePrefix x i.val) u (x i) else 0) := by
    intro i
    let m := i.val
    have hmM : m < M := i.isLt
    change uniformMean (fun x : Hist n M =>
        if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
        then beta q (tuplePrefix x m) u else 0) ≤
      c * uniformMean (fun x : Hist n M =>
        if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
        then creditIncrement q (tuplePrefix x m) u (x ⟨m, hmM⟩) else 0)
    have hm : m ∈ Finset.range M := Finset.mem_range.mpr hmM
    have hmle : m ≤ M := Nat.le_of_lt hmM
    have hm1le : m + 1 ≤ M := Nat.succ_le_iff.mpr hmM
    let J : Hist n m → ℝ := fun y =>
      indicator (T (padHist e₀ y) ≤ (m : WithTop ℕ))
    let C : Hist n m → ℝ := fun y => indicator (Colorable q (prefixGraph (M := M) e₀ y))
    let B : Hist n m → ℝ := fun y => beta q (prefixGraph (M := M) e₀ y) u
    let Z : Hist n m → Edge n → ℝ := fun y e => creditIncrement q (prefixGraph (M := M) e₀ y) u e
    have hstopPrefix (x : Hist n M) :
        (T x ≤ (m : WithTop ℕ)) ↔ J (takePrefix hmle x) = 1 := by
      have hfac := hT m (padHist e₀ (takePrefix hmle x)) x
        (fun i hi => padHist_eq e₀ hmle x i hi)
      change (T (padHist e₀ (takePrefix hmle x)) ≤ (m : WithTop ℕ)) ↔
        (T x ≤ (m : WithTop ℕ)) at hfac
      constructor
      · intro hs
        have hp : T (padHist e₀ (takePrefix hmle x)) ≤ (m : WithTop ℕ) := hfac.mpr hs
        simp [J, indicator, hp]
      · intro hs
        have hp : T (padHist e₀ (takePrefix hmle x)) ≤ (m : WithTop ℕ) := by
          simpa [J, indicator] using hs
        exact hfac.mp hp
    have hJid (x : Hist n M) :
        J (takePrefix hmle x) = indicator (T x ≤ (m : WithTop ℕ)) := by
      have hfac := hT m (padHist e₀ (takePrefix hmle x)) x
        (fun i hi => padHist_eq e₀ hmle x i hi)
      change (T (padHist e₀ (takePrefix hmle x)) ≤ (m : WithTop ℕ)) ↔
        (T x ≤ (m : WithTop ℕ)) at hfac
      by_cases hs : T x ≤ (m : WithTop ℕ)
      · have hp := hfac.mpr hs
        simp [J, indicator, hp, hs]
      · have hp : ¬ (T (padHist e₀ (takePrefix hmle x)) ≤ (m : WithTop ℕ)) := by
          intro hp
          exact hs (hfac.mp hp)
        simp [J, indicator, hp, hs]
    have hgraphPrefix (x : Hist n M) :
        tuplePrefix x m = prefixGraph (M := M) e₀ (takePrefix hmle x) :=
      tuplePrefix_factor e₀ hmle x
    have hleftRep :
        uniformMean (fun x : Hist n M =>
          if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
          then beta q (tuplePrefix x m) u else 0) =
        uniformMean (fun y : Hist n m => J y * C y * B y) := by
      have hp := h01bHist.1 m M hmle (fun y => J y * C y * B y)
      rw [← hp]
      apply congrArg uniformMean
      funext x
      rw [hgraphPrefix x]
      rw [hJid x]
      by_cases hs : T x ≤ (m : WithTop ℕ) <;>
        by_cases hc : Colorable q (prefixGraph (M := M) e₀ (takePrefix hmle x)) <;>
        simp [C, B, indicator, hs, hc]
    have hbeta : ∀ y : Hist n m,
        J y * C y * B y ≤ c * (J y * uniformMean (Z y)) := by
      intro y
      have hb := h25 n q hn hq (prefixGraph (M := M) e₀ y) u
      by_cases hcol : Colorable q (prefixGraph (M := M) e₀ y)
      · have hJnonneg : 0 ≤ J y := by
          by_cases hs : T (padHist e₀ y) ≤ (m : WithTop ℕ) <;>
            simp [J, indicator, hs]
        have hmul := mul_le_mul_of_nonneg_left hb hJnonneg
        have hmul' : J y * B y ≤ J y * (c * uniformMean (Z y)) := by
          simpa [B, Z, c] using hmul
        calc
          J y * C y * B y = J y * B y := by simp [C, hcol, indicator]
          _ ≤ J y * (c * uniformMean (Z y)) := hmul'
          _ = c * (J y * uniformMean (Z y)) := by ring
      · have hbetaZero : beta q (prefixGraph (M := M) e₀ y) u = 0 := by
          simp [beta, relation, hcol]
        simp [B, C, Z, creditIncrement, hcol, hbetaZero, uniformMean]
    have hprefixIneq := uniformMean_mono (h01a (Hist n m)) hbeta
    have hnext := h01bHist.2 m J Z
    have hcreditOnStep :
        uniformMean (fun y : Hist n (m + 1) =>
          J (takePrefix (Nat.le_succ m) y) *
            Z (takePrefix (Nat.le_succ m) y)
              (y ⟨m, Nat.lt_succ_self m⟩)) =
        uniformMean (fun y : Hist n m => J y * uniformMean (Z y)) := hnext
    let H : Hist n (m + 1) → ℝ := fun y =>
      J (takePrefix (Nat.le_succ m) y) *
        Z (takePrefix (Nat.le_succ m) y) (y ⟨m, Nat.lt_succ_self m⟩)
    have hExt := h01bHist.1 (m + 1) M hm1le H
    have hcreditExtend :
        uniformMean (fun x : Hist n M => H (takePrefix hm1le x)) =
          uniformMean (fun x : Hist n M =>
            if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
            then creditIncrement q (tuplePrefix x m) u (x ⟨m, hmM⟩) else 0) := by
      apply congrArg uniformMean
      funext x
      dsimp [H]
      have hprefix : takePrefix (Nat.le_succ m) (takePrefix hm1le x) = takePrefix hmle x := by
        funext j
        apply congrArg x
        apply Fin.ext
        rfl
      rw [hprefix]
      rw [hgraphPrefix x]
      have hcoord :
          (takePrefix hm1le x) ⟨m, Nat.lt_succ_self m⟩ = x ⟨m, hmM⟩ := by
        apply congrArg x
        apply Fin.ext
        rfl
      rw [hcoord]
      rw [hJid x]
      by_cases hs : T x ≤ (m : WithTop ℕ)
      · by_cases hc : Colorable q (prefixGraph (M := M) e₀ (takePrefix hmle x))
        · simp [Z, indicator, hs, hc]
        · simp [Z, indicator, hs, hc, creditIncrement]
      · by_cases hc : Colorable q (prefixGraph (M := M) e₀ (takePrefix hmle x))
        · simp [Z, indicator, hs, hc]
        · simp [Z, indicator, hs, hc, creditIncrement]
    calc
      _ = uniformMean (fun y : Hist n m => J y * C y * B y) := hleftRep
      _ ≤ c * uniformMean (fun y : Hist n m => J y * uniformMean (Z y)) := by
        rw [← (h01a (Hist n m)).smul c (fun y => J y * uniformMean (Z y))]
        exact hprefixIneq
      _ = c * uniformMean H := by rw [hcreditOnStep]
      _ = c * uniformMean (fun x : Hist n M => H (takePrefix hm1le x)) := by
        rw [hExt]
      _ = c * uniformMean (fun x : Hist n M =>
          if T x ≤ (m : WithTop ℕ) ∧ Colorable q (tuplePrefix x m)
          then creditIncrement q (tuplePrefix x m) u (x ⟨m, hmM⟩) else 0) := by
        rw [hcreditExtend]

  have hsumTerm :
      (∑ i : Fin M, uniformMean (fun x : Hist n M =>
        if T x ≤ (i.val : WithTop ℕ) ∧ Colorable q (tuplePrefix x i.val)
        then beta q (tuplePrefix x i.val) u else 0)) ≤
      c * (∑ i : Fin M, uniformMean (fun x : Hist n M =>
        if T x ≤ (i.val : WithTop ℕ) ∧ Colorable q (tuplePrefix x i.val)
        then creditIncrement q (tuplePrefix x i.val) u (x i) else 0)) := by
    calc
      _ ≤ ∑ i : Fin M, c * uniformMean (fun x : Hist n M =>
          if T x ≤ (i.val : WithTop ℕ) ∧ Colorable q (tuplePrefix x i.val)
          then creditIncrement q (tuplePrefix x i.val) u (x i) else 0) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by rw [Finset.mul_sum]
  have hoccExpand :
      uniformMean (stoppedOccupation q u T) =
        ∑ i : Fin M, uniformMean (fun x : Hist n M =>
          if T x ≤ (i.val : WithTop ℕ) ∧ Colorable q (tuplePrefix x i.val)
          then beta q (tuplePrefix x i.val) u else 0) := by
    unfold stoppedOccupation
    rw [← uniformMean_sum_fin]
    congr 1
    funext x
    rw [← Fin.sum_univ_eq_sum_range]
  have hcredSum :
      (∑ i : Fin M, uniformMean (fun x : Hist n M =>
        if T x ≤ (i.val : WithTop ℕ) ∧ Colorable q (tuplePrefix x i.val)
        then creditIncrement q (tuplePrefix x i.val) u (x i) else 0)) =
       uniformMean (fun x : Hist n M => suffixCredits q u (T x) x) := by
    rw [← uniformMean_sum_fin]
    apply congrArg uniformMean
    funext x
    unfold suffixCredits
    rfl
  have hsuffixPoint : ∀ x : Hist n M,
      suffixCredits q u (T x) x ≤ Real.log n * indicator (activeStart q T x) := by
    intro x
    exact h27 n q M hn hq u x (T x)
  have hsuffixMean := uniformMean_mono h01aHist hsuffixPoint
  have hprobMean : uniformMean (fun x : Hist n M => indicator (activeStart q T x)) =
      uniformProb (activeStart q T) := rfl
  have hlogMean := (h01aHist).smul (Real.log n)
    (fun x : Hist n M => indicator (activeStart q T x))
  have hfinal : uniformMean (fun x : Hist n M => suffixCredits q u (T x) x) ≤
      Real.log n * uniformProb (activeStart q T) := by
    calc
      _ ≤ uniformMean (fun x : Hist n M => Real.log n * indicator (activeStart q T x)) :=
        hsuffixMean
      _ = Real.log n * uniformProb (activeStart q T) := by rw [hlogMean, hprobMean]
  calc
    uniformMean (stoppedOccupation q u T) ≤ c * uniformMean (fun x : Hist n M => suffixCredits q u (T x) x) := by
      rw [hoccExpand]
      calc
        _ ≤ c * (∑ i : Fin M, uniformMean (fun x : Hist n M =>
            if T x ≤ (i.val : WithTop ℕ) ∧ Colorable q (tuplePrefix x i.val)
            then creditIncrement q (tuplePrefix x i.val) u (x i) else 0)) := hsumTerm
        _ = c * uniformMean (fun x : Hist n M => suffixCredits q u (T x) x) := by
          rw [hcredSum]
    _ ≤ c * (Real.log n * uniformProb (activeStart q T)) :=
      mul_le_mul_of_nonneg_left hfinal hcoef
    _ = (2 / Real.log 2) * Real.log n * uniformProb (activeStart q T) := by
      dsimp [c]
      ring

end ThLean.W.S629

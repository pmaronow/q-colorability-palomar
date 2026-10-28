import ThLean.BP.S6.Measure

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations MeasureTheory ProbabilityTheory
namespace ThLean.W.S630

private theorem tupleGraph_takePrefix_eq {n M m : ℕ} (hm : m ≤ M)
    (x : ThLean.BP.S6.Hist n M) :
    tupleGraph (ThLean.BP.S6.takePrefix hm x) = tuplePrefix x m := by
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  ext e
  simp only [tupleGraph, tuplePrefix]
  refine Finset.card_bij'
    (fun i _ => (⟨i.val, lt_of_lt_of_le i.isLt hm⟩ : Fin M))
    (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2.1⟩ : Fin m))
    ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    constructor
    · exact i.isLt
    · simpa [ThLean.BP.S6.takePrefix] using hi
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simpa [ThLean.BP.S6.takePrefix] using hj.2
  · intro i hi
    apply Fin.ext
    rfl
  · intro j hj
    apply Fin.ext
    rfl

private theorem processGraph_prefix {n M m : ℕ} {Ω : Type} (hm : m ≤ M)
    (e : ℕ → Ω → ThLean.BP.S6.Edge n) (ω : Ω) :
    processGraph (fun i => e i ω) m =
      tuplePrefix (ThLean.BP.S6.inputPrefix e M ω) m := by
  rw [processGraph]
  have hfun : (fun i : Fin m => e i.val ω) =
      ThLean.BP.S6.takePrefix hm (ThLean.BP.S6.inputPrefix e M ω) := by
    funext i
    rfl
  rw [hfun]
  exact tupleGraph_takePrefix_eq hm _

private theorem firstFailure_le_iff (P : ℕ → Prop) (m : ℕ) :
    firstFailure P ≤ (m : WithTop ℕ) ↔ ∃ k ≤ m, P k := by
  classical
  by_cases h : ∃ k, P k
  · simp [firstFailure, h, Nat.find_le_iff h]
  · have hn : ¬ ∃ k ≤ m, P k := by
      rintro ⟨k, hkm, hPk⟩
      exact h ⟨k, hPk⟩
    simp [firstFailure, h, hn]

private theorem finiteHitting_le_iff {n M m : ℕ} (q : ℕ)
    (x : ThLean.BP.S6.Hist n M) (hm : m < M) :
    finiteHittingTime q x ≤ m ↔ ∃ k ≤ m, ¬ Colorable q (tuplePrefix x k) := by
  classical
  unfold finiteHittingTime
  split_ifs with h
  · rw [Nat.find_le_iff h]
    constructor
    · rintro ⟨k, hkm, hkM, hbad⟩
      exact ⟨k, hkm, hbad⟩
    · rintro ⟨k, hkm, hbad⟩
      exact ⟨k, hkm, le_trans hkm (Nat.le_of_lt hm), hbad⟩
  · constructor
    · intro hle
      omega
    · rintro ⟨k, hkm, hbad⟩
      exact False.elim (h ⟨k, le_trans hkm (Nat.le_of_lt hm), hbad⟩)

private theorem hittingThreshold_eq {n M m : ℕ} {Ω : Type}
    (q : ℕ) (e : ℕ → Ω → ThLean.BP.S6.Edge n) (ω : Ω)
    (hm : m < M) :
    hittingTime q (fun i => e i ω) ≤ (m : WithTop ℕ) ↔
      finiteHittingTime q (ThLean.BP.S6.inputPrefix e M ω) ≤ m := by
  rw [show hittingTime q (fun i => e i ω) =
      firstFailure (fun k => ¬ Colorable q (processGraph (fun i => e i ω) k)) by rfl]
  rw [firstFailure_le_iff, finiteHitting_le_iff q _ hm]
  constructor
  · rintro ⟨k, hkm, hbad⟩
    refine ⟨k, hkm, ?_⟩
    have hkM : k ≤ M := le_trans hkm (Nat.le_of_lt hm)
    rw [processGraph_prefix hkM e ω] at hbad
    exact hbad
  · rintro ⟨k, hkm, hbad⟩
    refine ⟨k, hkm, ?_⟩
    have hkM : k ≤ M := le_trans hkm (Nat.le_of_lt hm)
    rw [processGraph_prefix hkM e ω]
    exact hbad

private theorem minWithTop_le_iff_of_lt {a : WithTop ℕ} {m M : ℕ}
    (hm : m < M) : min a (M : WithTop ℕ) ≤ (m : WithTop ℕ) ↔
      a ≤ (m : WithTop ℕ) := by
  rw [min_le_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact False.elim ((not_le_of_gt (WithTop.coe_lt_coe.mpr hm)) h)
  · intro h
    exact Or.inl h

private theorem natMin_le_iff_of_lt {a m M : ℕ} (hm : m < M) :
    min a M ≤ m ↔ a ≤ m := by
  constructor
  · intro h
    by_cases ha : a ≤ M
    · rw [Nat.min_eq_left ha] at h
      exact h
    · rw [Nat.min_eq_right (Nat.le_of_not_ge ha)] at h
      omega
  · intro h
    exact (min_le_left a M).trans h

private theorem stoppedTime_le_iff {n M m : ℕ} {Ω : Type}
    (q : ℕ) (e : ℕ → Ω → ThLean.BP.S6.Edge n) (ω : Ω)
    (hm : m < M) :
    ThresholdFoundations.stoppedTime q M (fun i => e i ω) ≤ (m : WithTop ℕ) ↔
      hittingTime q (fun i => e i ω) ≤ (m : WithTop ℕ) := by
  change min (hittingTime q (fun i => e i ω)) (M : WithTop ℕ) ≤
      (m : WithTop ℕ) ↔ _
  exact minWithTop_le_iff_of_lt hm

private theorem finiteStop_le_iff {n M m : ℕ} (q : ℕ)
    (x : ThLean.BP.S6.Hist n M) (hm : m < M) :
    (ThLean.BP.S6.finiteStop q x : WithTop ℕ) ≤ (m : WithTop ℕ) ↔
      finiteHittingTime q x ≤ m := by
  change ((min (finiteHittingTime q x) M : ℕ) : WithTop ℕ) ≤
      (m : WithTop ℕ) ↔ _
  constructor
  · intro h
    exact (natMin_le_iff_of_lt hm).mp (WithTop.coe_le_coe.mp h)
  · intro h
    exact WithTop.coe_le_coe.mpr ((natMin_le_iff_of_lt hm).mpr h)

private theorem boundedWithTop_eq_of_thresholds {a b : WithTop ℕ} {M : ℕ}
    (ha : a ≤ (M : WithTop ℕ)) (hb : b ≤ (M : WithTop ℕ))
    (h : ∀ m, m < M → (a ≤ (m : WithTop ℕ) ↔ b ≤ (m : WithTop ℕ))) :
    a = b := by
  cases a with
  | top => simp at ha
  | coe a =>
    cases b with
    | top => simp at hb
    | coe b =>
      have ha' : a ≤ M := WithTop.coe_le_coe.mp ha
      have hb' : b ≤ M := WithTop.coe_le_coe.mp hb
      have hab : a ≤ b := by
        by_cases hlt : b < M
        · exact WithTop.coe_le_coe.mp ((h b hlt).mpr (by simp))
        · omega
      have hba : b ≤ a := by
        by_cases hlt : a < M
        · exact WithTop.coe_le_coe.mp ((h a hlt).mp (by simp))
        · omega
      exact congrArg (fun k : ℕ => (k : WithTop ℕ)) (Nat.le_antisymm hab hba)

private theorem withTop_lt_nat_iff_le_pred {a : WithTop ℕ} {r : ℕ}
    (hr : 0 < r) : a < (r : WithTop ℕ) ↔ a ≤ ((r - 1 : ℕ) : WithTop ℕ) := by
  cases a with
  | top => simp
  | coe a =>
    constructor
    · intro hlt
      have hlt' : a < r := WithTop.coe_lt_coe.mp hlt
      have hle : a ≤ r - 1 := by omega
      exact WithTop.coe_le_coe.mpr hle
    · intro hle
      have hle' : a ≤ r - 1 := WithTop.coe_le_coe.mp hle
      have hlt : a < r := by omega
      exact WithTop.coe_lt_coe.mpr hlt

private theorem lt_iff_of_thresholds {a b : WithTop ℕ} {r M : ℕ}
    (hrM : r ≤ M) (hab : ∀ m, m < M → (a ≤ (m : WithTop ℕ) ↔ b ≤ (m : WithTop ℕ))) :
    a < (r : WithTop ℕ) ↔ b < (r : WithTop ℕ) := by
  by_cases hr : r = 0
  · simp [hr]
  · have hrpos : 0 < r := by omega
    have hpred : r - 1 < M := by omega
    rw [withTop_lt_nat_iff_le_pred hrpos, hab (r - 1) hpred,
      withTop_lt_nat_iff_le_pred hrpos]

private theorem stoppingThreshold_prefix {n M m : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (e : ℕ → Ω → ThLean.BP.S6.Edge n)
    (T : Ω → WithTop ℕ) (hT : ThLean.BP.S6.InputStoppingTime e T)
    (hm : m < M) (x y : ThLean.BP.S6.Hist n M) (ωx ωy : Ω)
    (hx : ThLean.BP.S6.inputPrefix e M ωx = x)
    (hy : ThLean.BP.S6.inputPrefix e M ωy = y)
    (hxy : ∀ i : Fin M, i.val < m → x i = y i) :
    (T ωx ≤ (m : WithTop ℕ) ↔ T ωy ≤ (m : WithTop ℕ)) := by
  have hpref : ThLean.BP.S6.inputPrefix e m ωx =
      ThLean.BP.S6.inputPrefix e m ωy := by
    funext i
    have hiM : i.val < M := lt_of_lt_of_le i.isLt (Nat.le_of_lt hm)
    have hx' := congrFun hx (⟨i.val, hiM⟩ : Fin M)
    have hy' := congrFun hy (⟨i.val, hiM⟩ : Fin M)
    have hxy' := hxy ⟨i.val, hiM⟩ i.isLt
    simpa [ThLean.BP.S6.inputPrefix] using hx'.trans (hxy'.trans hy'.symm)
  have hmeas : MeasurableSet[MeasurableSpace.comap (ThLean.BP.S6.inputPrefix e m) ⊤]
      {ω | T ω ≤ (m : WithTop ℕ)} := hT m
  rw [MeasurableSpace.measurableSet_comap] at hmeas
  obtain ⟨A, hA, hpre⟩ := hmeas
  have hωx : T ωx ≤ (m : WithTop ℕ) ↔ ThLean.BP.S6.inputPrefix e m ωx ∈ A := by
    change ωx ∈ {ω | T ω ≤ (m : WithTop ℕ)} ↔ _
    rw [← hpre]
    rfl
  have hωy : T ωy ≤ (m : WithTop ℕ) ↔ ThLean.BP.S6.inputPrefix e m ωy ∈ A := by
    change ωy ∈ {ω | T ω ≤ (m : WithTop ℕ)} ↔ _
    rw [← hpre]
    rfl
  rw [hωx, hωy, hpref]

private theorem prefix_realized {n M : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : ℕ → Ω → ThLean.BP.S6.Edge n)
    (he : ThLean.BP.S6.UniformStream μ e)
    (h02a : ThLean.BP.S6.S6_02aStatement) (hn : 3 ≤ n)
    (x : ThLean.BP.S6.Hist n M) :
    ∃ ω, ThLean.BP.S6.inputPrefix e M ω = x := by
  have hmass : μ.real {ω | (fun i : Fin M => e i.val ω) = x} =
      1 / (Fintype.card (ThLean.BP.S6.Hist n M) : ℝ) :=
    h02a n M hn Ω μ (fun i : Fin M => e i.val) (he M) x
  have hset : {ω | ThLean.BP.S6.inputPrefix e M ω = x} =
      {ω | (fun i : Fin M => e i.val ω) = x} := by
    ext ω
    rfl
  have hpos : 0 < μ.real {ω | ThLean.BP.S6.inputPrefix e M ω = x} := by
    rw [hset, hmass]
    apply one_div_pos.mpr
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨x⟩)
  exact MeasureTheory.nonempty_of_measureReal_ne_zero hpos.ne'

theorem S6_29aStatement_of_deps (h02a : ThLean.BP.S6.S6_02aStatement) :
    ThLean.BP.S6.S6_29aStatement := by
  classical
  intro n q M hn hq Ω _ μ _ e T u he hT
  let rep : ThLean.BP.S6.Hist n M → Ω := fun x =>
    Classical.choose (prefix_realized μ e he h02a hn x)
  have hrep : ∀ x, ThLean.BP.S6.inputPrefix e M (rep x) = x := by
    intro x
    exact Classical.choose_spec (prefix_realized μ e he h02a hn x)
  let S : ThLean.BP.S6.Hist n M → WithTop ℕ := fun x => T (rep x)
  have hfinite : IsFiniteStoppingTime S := by
    intro m x y hxy
    by_cases hm : m < M
    · exact stoppingThreshold_prefix e T hT hm x y (rep x) (rep y)
        (hrep x) (hrep y) hxy
    · have hxy' : x = y := by
        funext i
        exact hxy i (by omega)
      subst y
      rfl
  have hvalue : ∀ ω, ThLean.BP.S6.sampledOccupation q M u e T ω =
      stoppedOccupation q u S (ThLean.BP.S6.inputPrefix e M ω) := by
    intro ω
    let x := ThLean.BP.S6.inputPrefix e M ω
    have hthreshold (m : ℕ) (hm : m < M) :
        S x ≤ (m : WithTop ℕ) ↔ T ω ≤ (m : WithTop ℕ) := by
      exact stoppingThreshold_prefix e T hT hm x x (rep x) ω
        (hrep x) rfl (fun _ _ => rfl)
    unfold ThLean.BP.S6.sampledOccupation stoppedOccupation
    apply Finset.sum_congr rfl
    intro m hm
    have hmM : m < M := Finset.mem_range.mp hm
    rw [processGraph_prefix (Nat.le_of_lt hmM) e ω]
    by_cases hTω : T ω ≤ (m : WithTop ℕ)
    · have hSx : S x ≤ (m : WithTop ℕ) := (hthreshold m hmM).mpr hTω
      simp [hTω, hSx, x]
    · have hSx : ¬ S x ≤ (m : WithTop ℕ) := fun h =>
        hTω ((hthreshold m hmM).mp h)
      simp [hTω, hSx, x]
  have hstop (ω : Ω) :
      ThresholdFoundations.stoppedTime q M (fun i => e i ω) =
        (ThLean.BP.S6.finiteStop q (ThLean.BP.S6.inputPrefix e M ω) : WithTop ℕ) := by
    let x := ThLean.BP.S6.inputPrefix e M ω
    have hrawBound : ThresholdFoundations.stoppedTime q M (fun i => e i ω) ≤
        (M : WithTop ℕ) := by
      simp [ThresholdFoundations.stoppedTime]
    have hfinBound : (ThLean.BP.S6.finiteStop q x : WithTop ℕ) ≤
        (M : WithTop ℕ) := by
      exact_mod_cast (Nat.min_le_right (finiteHittingTime q x) M)
    apply boundedWithTop_eq_of_thresholds hrawBound hfinBound
    intro m hm
    rw [stoppedTime_le_iff q e ω hm, finiteStop_le_iff q x hm]
    exact hittingThreshold_eq q e ω hm
  have hevent : ∀ ω, ThLean.BP.S6.sampledActive q M e T ω ↔
      ThLean.BP.S6.activeStart q S (ThLean.BP.S6.inputPrefix e M ω) := by
    intro ω
    let x := ThLean.BP.S6.inputPrefix e M ω
    have hthreshold (m : ℕ) (hm : m < M) :
        S x ≤ (m : WithTop ℕ) ↔ T ω ≤ (m : WithTop ℕ) := by
      exact stoppingThreshold_prefix e T hT hm x x (rep x) ω
        (hrep x) rfl (fun _ _ => rfl)
    have hstop' := hstop ω
    unfold ThLean.BP.S6.sampledActive ThLean.BP.S6.activeStart
    rw [hstop']
    have hbound : ThLean.BP.S6.finiteStop q x ≤ M := by
      exact Nat.min_le_right _ _
    exact (lt_iff_of_thresholds hbound hthreshold).symm
  exact ⟨S, hfinite, hvalue, hevent⟩

end ThLean.W.S630

example (h02a : ThLean.BP.S6.S6_02aStatement) :
    ThLean.BP.S6.S6_29aStatement := ThLean.W.S630.S6_29aStatement_of_deps h02a

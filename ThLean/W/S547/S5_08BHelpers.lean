import ThLean.BP.S5.Poisson

set_option maxHeartbeats 600000

noncomputable section
open scoped BigOperators ENNReal

namespace ThLean.W.S547

open ThresholdFoundations
open ThLean.BP.S5

lemma pair_not_diag_iff {V : Type} (e : Sym2 V) :
    (∀ v : V, e ≠ s(v, v)) ↔ ¬ e.IsDiag := by
  refine Sym2.ind ?_ e
  intro a b
  simp [Sym2.IsDiag, eq_comm]

lemma pair_card_eq_choose_two (V : Type) [Fintype V] [Fintype (Pair V)] :
    Fintype.card (Pair V) = (Fintype.card V).choose 2 := by
  classical
  let e : Pair V ≃ {x : Sym2 V // ¬ x.IsDiag} :=
    { toFun := fun x => ⟨x.1, (pair_not_diag_iff x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (pair_not_diag_iff x.1).mpr x.2⟩
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; cases x; rfl }
  rw [Fintype.card_congr e, Sym2.card_subtype_not_diag]

lemma looplessRate_eq_perPairRate {V : Type} [Fintype V]
    (t : ℝ) (hV : 2 ≤ Fintype.card V) :
    looplessRate (V := V) t = perPairRate (V := V)
      (t / ((Fintype.card V).choose 2 : ℝ)) := by
  classical
  have hcard : (Fintype.card (Pair V) : ℝ) = ((Fintype.card V).choose 2 : ℝ) := by
    exact_mod_cast pair_card_eq_choose_two V
  funext e
  have hmem : (e ∈ completeEdges (V := V)) ↔ ¬ ∃ v : V, e = s(v, v) := by
    simp [completeEdges]
  by_cases hd : ∃ v : V, e = s(v, v)
  · simp [looplessRate, perPairRate, hmem, hd]
  · simp [looplessRate, perPairRate, hmem, hd, hcard]

lemma uniformMeanENN_ofReal {α : Type} [Fintype α] [Nonempty α]
    (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    uniformMeanENN (fun a => ENNReal.ofReal (g a)) = ENNReal.ofReal (uniformMean g) := by
  have hc : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty α))
  simp [uniformMeanENN, uniformMean, ENNReal.ofReal_div_of_pos hc,
    ENNReal.ofReal_sum_of_nonneg (fun a ha => hg a)]

lemma uniformMean_bounds {α : Type} [Fintype α] [Nonempty α]
    (g : α → ℝ) (C : ℝ) (h0 : ∀ a, 0 ≤ g a) (hC : ∀ a, g a ≤ C) :
    0 ≤ uniformMean g ∧ uniformMean g ≤ C := by
  have hc : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty α))
  have hsum0 : 0 ≤ ∑ a, g a := Finset.sum_nonneg fun a ha => h0 a
  have hsumC : (∑ a, g a) ≤ (Fintype.card α : ℝ) * C := by
    calc
      (∑ a, g a) ≤ ∑ _a : α, C := Finset.sum_le_sum fun a ha => hC a
      _ = (Fintype.card α : ℝ) * C := by simp
  constructor
  · unfold uniformMean
    exact div_nonneg hsum0 (by positivity)
  · unfold uniformMean
    exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hsumC)

lemma poissonGraphMeanENN_ofReal_toReal
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (hE01 : ThLean.BP.S5.S5_E01Statement) (t C : ℝ)
    (ht : 0 ≤ t) (g : MGraph V → ℝ)
    (hg0 : ∀ G, 0 ≤ g G) (hgC : ∀ G, g G ≤ C) :
    poissonGraphMean t g =
      (poissonGraphMeanENN t (fun G => ENNReal.ofReal (g G))).toReal := by
  classical
  have hpairCard : Fintype.card (Pair V) = (Fintype.card V).choose 2 :=
    pair_card_eq_choose_two V
  have hpairPos : 0 < Fintype.card (Pair V) := by
    rw [hpairCard]
    exact Nat.choose_pos (by omega)
  letI : Nonempty (Pair V) := Fintype.card_pos_iff.mp hpairPos
  have hweights := (hE01.1 t ht)
  have hweightNonneg : ∀ m, 0 ≤ poissonWeight t m := fun m => (hweights.1 m).1
  have hweightSum : HasSum (poissonWeight t) 1 := hweights.2.1
  have hweightENN : (∑' m, ENNReal.ofReal (poissonWeight t m)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hweightNonneg hweightSum.summable]
    rw [hweightSum.tsum_eq]
    simp
  let a : ℕ → ℝ := fun m => uniformMean (fun x : EdgeTuple V m => g (tupleGraph x))
  have haBounds (m : ℕ) : 0 ≤ a m ∧ a m ≤ C := by
    apply uniformMean_bounds
    · intro x
      exact hg0 (tupleGraph x)
    · intro x
      exact hgC (tupleGraph x)
  have hmeanENN (m : ℕ) :
      uniformMeanENN (fun x : EdgeTuple V m => ENNReal.ofReal (g (tupleGraph x))) =
        ENNReal.ofReal (a m) := by
    dsimp [a]
    apply uniformMeanENN_ofReal
    intro x
    exact hg0 (tupleGraph x)
  have htermBound (m : ℕ) :
      ENNReal.ofReal (poissonWeight t m) *
          uniformMeanENN (fun x : EdgeTuple V m => ENNReal.ofReal (g (tupleGraph x))) ≤
        ENNReal.ofReal C * ENNReal.ofReal (poissonWeight t m) := by
    rw [hmeanENN]
    calc
      ENNReal.ofReal (poissonWeight t m) * ENNReal.ofReal (a m) ≤
          ENNReal.ofReal (poissonWeight t m) * ENNReal.ofReal C :=
            mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (haBounds m).2) (by positivity)
      _ = ENNReal.ofReal C * ENNReal.ofReal (poissonWeight t m) := by ac_rfl
  have hbound :
      (∑' m, ENNReal.ofReal (poissonWeight t m) *
          uniformMeanENN (fun x : EdgeTuple V m => ENNReal.ofReal (g (tupleGraph x)))) ≤
        ENNReal.ofReal C := by
    calc
      _ ≤ ∑' m, ENNReal.ofReal C * ENNReal.ofReal (poissonWeight t m) :=
        ENNReal.tsum_le_tsum fun m => htermBound m
      _ = ENNReal.ofReal C := by rw [ENNReal.tsum_mul_left, hweightENN, mul_one]
  have hfinite :
      (∑' m, ENNReal.ofReal (poissonWeight t m) *
          uniformMeanENN (fun x : EdgeTuple V m => ENNReal.ofReal (g (tupleGraph x)))) ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)
  have htermToReal (m : ℕ) :
      (ENNReal.ofReal (poissonWeight t m) *
          uniformMeanENN (fun x : EdgeTuple V m => ENNReal.ofReal (g (tupleGraph x)))).toReal =
        poissonWeight t m * a m := by
    rw [hmeanENN, ← ENNReal.ofReal_mul (hweightNonneg m)]
    exact ENNReal.toReal_ofReal (mul_nonneg (hweightNonneg m) (haBounds m).1)
  change (∑' m, poissonWeight t m * a m) =
    (∑' m, ENNReal.ofReal (poissonWeight t m) *
      uniformMeanENN (fun x : EdgeTuple V m => ENNReal.ofReal (g (tupleGraph x)))).toReal
  symm
  rw [ENNReal.tsum_toReal_eq (fun m => by
    rw [hmeanENN]
    exact ENNReal.mul_ne_top (by simp) (by simp))]
  simp_rw [htermToReal]

lemma poissonGraphMeanENN_one
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (hE01 : ThLean.BP.S5.S5_E01Statement) (t : ℝ) (ht : 0 ≤ t) :
    poissonGraphMeanENN t (fun _ : MGraph V => (1 : ℝ≥0∞)) = 1 := by
  classical
  have hpairCard : Fintype.card (Pair V) = (Fintype.card V).choose 2 :=
    pair_card_eq_choose_two V
  have hpairPos : 0 < Fintype.card (Pair V) := by
    rw [hpairCard]
    exact Nat.choose_pos (by omega)
  letI : Nonempty (Pair V) := Fintype.card_pos_iff.mp hpairPos
  have hweights := (hE01.1 t ht)
  have hweightNonneg : ∀ m, 0 ≤ poissonWeight t m := fun m => (hweights.1 m).1
  have hweightSum : HasSum (poissonWeight t) 1 := hweights.2.1
  have hweightENN : (∑' m, ENNReal.ofReal (poissonWeight t m)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hweightNonneg hweightSum.summable]
    rw [hweightSum.tsum_eq]
    simp
  have hmean (m : ℕ) :
      uniformMeanENN (fun _ : EdgeTuple V m => (1 : ℝ≥0∞)) = 1 := by
    have h := uniformMeanENN_ofReal (fun _ : EdgeTuple V m => (1 : ℝ)) (by intro x; norm_num)
    simpa [uniformMean] using h
  change ∑' m, ENNReal.ofReal (poissonWeight t m) *
    uniformMeanENN (fun _ : EdgeTuple V m => (1 : ℝ≥0∞)) = 1
  simp_rw [hmean]
  rw [ENNReal.tsum_mul_right, mul_one, hweightENN]

lemma independentGraphMeanENN_ofReal_toReal
    {V : Type} [Fintype V] (rate : Sym2 V → ℝ) (C : ℝ) (g : MGraph V → ℝ)
    (hTotal : independentPoissonGraphMeanENN rate (fun _ => (1 : ℝ≥0∞)) = 1)
    (hmass0 : ∀ G, 0 ≤ independentPoissonGraphMass rate G)
    (hg0 : ∀ G, 0 ≤ g G) (hgC : ∀ G, g G ≤ C) :
    independentPoissonGraphMean rate g =
      (independentPoissonGraphMeanENN rate (fun G => ENNReal.ofReal (g G))).toReal := by
  classical
  have htermBound (G : MGraph V) :
      ENNReal.ofReal (independentPoissonGraphMass rate G) * ENNReal.ofReal (g G) ≤
        ENNReal.ofReal C * ENNReal.ofReal (independentPoissonGraphMass rate G) := by
    calc
      _ ≤ ENNReal.ofReal (independentPoissonGraphMass rate G) * ENNReal.ofReal C :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hgC G)) (by positivity)
      _ = _ := by ac_rfl
  have hbound :
      (∑' G : MGraph V,
        ENNReal.ofReal (independentPoissonGraphMass rate G) * ENNReal.ofReal (g G)) ≤
        ENNReal.ofReal C := by
    calc
      _ ≤ ∑' G : MGraph V,
          ENNReal.ofReal C * ENNReal.ofReal (independentPoissonGraphMass rate G) :=
        ENNReal.tsum_le_tsum fun G => htermBound G
      _ = ENNReal.ofReal C := by
        rw [ENNReal.tsum_mul_left]
        simpa [independentPoissonGraphMeanENN] using congrArg (fun x => ENNReal.ofReal C * x) hTotal
  have hfinite :
      (∑' G : MGraph V,
        ENNReal.ofReal (independentPoissonGraphMass rate G) * ENNReal.ofReal (g G)) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)
  have htermToReal (G : MGraph V) :
      (ENNReal.ofReal (independentPoissonGraphMass rate G) * ENNReal.ofReal (g G)).toReal =
        independentPoissonGraphMass rate G * g G := by
    rw [← ENNReal.ofReal_mul (hmass0 G)]
    exact ENNReal.toReal_ofReal (mul_nonneg (hmass0 G) (hg0 G))
  change (∑' G : MGraph V, independentPoissonGraphMass rate G * g G) =
    (∑' G : MGraph V,
      ENNReal.ofReal (independentPoissonGraphMass rate G) * ENNReal.ofReal (g G)).toReal
  symm
  rw [ENNReal.tsum_toReal_eq (fun G => ENNReal.mul_ne_top (by simp) (by simp))]
  simp_rw [htermToReal]

lemma looplessRate_nonneg {V : Type} [Fintype V]
    (t : ℝ) (ht : 0 ≤ t) (e : Sym2 V) : 0 ≤ looplessRate t e := by
  classical
  unfold looplessRate
  split_ifs <;> positivity

lemma looplessGraphMass_nonneg {V : Type} [Fintype V]
    (hE01 : ThLean.BP.S5.S5_E01Statement) (t : ℝ) (ht : 0 ≤ t)
    (G : MGraph V) : 0 ≤ independentPoissonGraphMass (looplessRate t) G := by
  classical
  unfold independentPoissonGraphMass
  exact Finset.prod_nonneg fun e he =>
    ((hE01.1 (looplessRate t e) (looplessRate_nonneg t ht e)).1 (G e)).1

lemma poissonGraphMean_series_summable
    {V : Type} [Fintype V] [Fintype (Pair V)] (hV : 2 ≤ Fintype.card V)
    (hE01 : ThLean.BP.S5.S5_E01Statement) (t C : ℝ)
    (ht : 0 ≤ t) (hC : 0 ≤ C) (g : MGraph V → ℝ)
    (hg0 : ∀ G, 0 ≤ g G) (hgC : ∀ G, g G ≤ C) :
    Summable (fun m => poissonWeight t m *
      uniformMean (fun x : EdgeTuple V m => g (tupleGraph x))) := by
  classical
  have hpairCard : Fintype.card (Pair V) = (Fintype.card V).choose 2 :=
    pair_card_eq_choose_two V
  have hpairPos : 0 < Fintype.card (Pair V) := by
    rw [hpairCard]
    exact Nat.choose_pos (by omega)
  letI : Nonempty (Pair V) := Fintype.card_pos_iff.mp hpairPos
  let a : ℕ → ℝ := fun m => uniformMean (fun x : EdgeTuple V m => g (tupleGraph x))
  have ha (m : ℕ) : 0 ≤ a m ∧ a m ≤ C := by
    apply uniformMean_bounds
    · intro x
      exact hg0 (tupleGraph x)
    · intro x
      exact hgC (tupleGraph x)
  simpa [a] using
    ((hE01.1 t ht).2.2.2 C a hC ha).1

lemma independentGraphMass_summable
    {V : Type} [Fintype V] (rate : Sym2 V → ℝ)
    (hTotal : independentPoissonGraphMeanENN rate (fun _ => (1 : ℝ≥0∞)) = 1)
    (hmass0 : ∀ G, 0 ≤ independentPoissonGraphMass rate G) :
    Summable (independentPoissonGraphMass rate) := by
  classical
  have hsumENN :
      (∑' G : MGraph V, ENNReal.ofReal (independentPoissonGraphMass rate G)) = 1 := by
    simpa [independentPoissonGraphMeanENN] using hTotal
  have hsumENN_ne_top :
      (∑' G : MGraph V, ENNReal.ofReal (independentPoissonGraphMass rate G)) ≠ ∞ := by
    rw [hsumENN]
    simp
  have hsumNN : Summable (fun G : MGraph V =>
      (ENNReal.ofReal (independentPoissonGraphMass rate G)).toNNReal) :=
    ENNReal.summable_toNNReal_of_tsum_ne_top hsumENN_ne_top
  have hsumRealNN : Summable (fun G : MGraph V =>
      ((ENNReal.ofReal (independentPoissonGraphMass rate G)).toNNReal : ℝ)) :=
    NNReal.summable_coe.mpr hsumNN
  apply hsumRealNN.congr
  intro G
  simp [ENNReal.ofReal, Real.toNNReal, hmass0 G]

lemma independentGraphMean_series_summable
    {V : Type} [Fintype V] (rate : Sym2 V → ℝ) (C : ℝ)
    (g : MGraph V → ℝ)
    (hmass0 : ∀ G, 0 ≤ independentPoissonGraphMass rate G)
    (hTotal : independentPoissonGraphMeanENN rate (fun _ => (1 : ℝ≥0∞)) = 1)
    (hg0 : ∀ G, 0 ≤ g G) (hgC : ∀ G, g G ≤ C) :
    Summable (fun G : MGraph V => independentPoissonGraphMass rate G * g G) := by
  have hmass := independentGraphMass_summable rate hTotal hmass0
  have hupper : Summable (fun G : MGraph V => C * independentPoissonGraphMass rate G) :=
    hmass.mul_left C
  apply Summable.of_nonneg_of_le (fun G => mul_nonneg (hmass0 G) (hg0 G))
    (fun G => ?_) hupper
  calc
    independentPoissonGraphMass rate G * g G ≤
        independentPoissonGraphMass rate G * C :=
      mul_le_mul_of_nonneg_left (hgC G) (hmass0 G)
    _ = C * independentPoissonGraphMass rate G := by ring

lemma poissonGraphMean_eq_countMean_nonneg
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (hPreSplit : ThresholdFoundations.PreSplitStatement.{0, 0})
    (hE01 : ThLean.BP.S5.S5_E01Statement) (t C : ℝ)
    (ht : 0 ≤ t) (g : MGraph V → ℝ)
    (hg0 : ∀ G, 0 ≤ g G) (hgC : ∀ G, g G ≤ C) :
    poissonGraphMean t g =
      countMean (t / ((Fintype.card V).choose 2 : ℝ)) g := by
  classical
  have hRate := looplessRate_eq_perPairRate t hV
  have hPoissonOne := poissonGraphMeanENN_one hV hE01 t ht
  have hTotal :
      independentPoissonGraphMeanENN (looplessRate t)
        (fun _ : MGraph V => (1 : ℝ≥0∞)) = 1 := by
    have h := hPreSplit.2.2.2 V hV t (fun _ => (1 : ℝ≥0∞)) ht
    rw [hPoissonOne] at h
    exact h.symm
  have hLaw := hPreSplit.2.2.2 V hV t
    (fun G => ENNReal.ofReal (g G)) ht
  have hPoisson := poissonGraphMeanENN_ofReal_toReal hV hE01 t C ht g hg0 hgC
  have hGraph := independentGraphMeanENN_ofReal_toReal
    (looplessRate t) C g hTotal (looplessGraphMass_nonneg hE01 t ht) hg0 hgC
  have hCount : countMean (t / ((Fintype.card V).choose 2 : ℝ)) g =
      (independentPoissonGraphMeanENN (looplessRate t)
        (fun G => ENNReal.ofReal (g G))).toReal := by
    unfold countMean
    rw [← hRate]
    exact hGraph
  calc
    poissonGraphMean t g =
        (poissonGraphMeanENN t (fun G => ENNReal.ofReal (g G))).toReal := hPoisson
    _ = (independentPoissonGraphMeanENN (looplessRate t)
        (fun G => ENNReal.ofReal (g G))).toReal := congrArg ENNReal.toReal hLaw
    _ = countMean (t / ((Fintype.card V).choose 2 : ℝ)) g := hCount.symm


end ThLean.W.S547

import ThLean.BP.S5.Occupation

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S545
open ThresholdFoundations ThLean.BP.S5

theorem lawMean_map_uniform {α β : Type*} [Nonempty α] [Fintype α]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β] [Nonempty β]
    (g : α → β) (f : β → ℝ) (hf : ∃ C : ℝ, ∀ b, |f b| ≤ C) :
    (∑' b, (PMF.map g (PMF.uniformOfFintype α) b).toReal * f b) =
      uniformMean (fun x => f (g x)) := by
  classical
  let p : PMF α := PMF.uniformOfFintype α
  let ν : PMF β := PMF.map g p
  have hg : Measurable g := measurable_of_countable g
  have hfm : Measurable f := measurable_of_countable f
  rcases hf with ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    have hb := hC (Classical.choice ‹Nonempty β›)
    exact le_trans (abs_nonneg _) hb
  have hνint : Integrable f ν.toMeasure := by
    apply (integrable_const C).mono' hfm.aestronglyMeasurable
    filter_upwards with b
    simpa [Real.norm_eq_abs] using hC b
  calc
    (∑' b, (ν b).toReal * f b) = ∫ b, f b ∂ν.toMeasure := by
      simpa only [smul_eq_mul] using (PMF.integral_eq_tsum ν f hνint).symm
    _ = ∫ x, f (g x) ∂p.toMeasure := by
      rw [← PMF.toMeasure_map g p hg]
      exact MeasureTheory.integral_map hg.aemeasurable hfm.aestronglyMeasurable
    _ = uniformMean (fun x => f (g x)) := by
      rw [PMF.integral_eq_sum p (fun x => f (g x))]
      rw [uniformMean]
      simp only [smul_eq_mul, p, PMF.uniformOfFintype_apply]
      rw [← Finset.mul_sum]
      simp [div_eq_mul_inv, ENNReal.toReal_inv]
      ring

lemma indicator_bounds (P : Prop) : 0 ≤ indicator P ∧ indicator P ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

lemma uniformMean_bounds {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 := by
  have hcard : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum0 : 0 ≤ ∑ a, f a := Finset.sum_nonneg fun a _ => (hf a).1
  have hsum1 : ∑ a, f a ≤ (Fintype.card α : ℝ) := by
    calc
      ∑ a, f a ≤ ∑ _a : α, (1 : ℝ) := Finset.sum_le_sum fun a _ => (hf a).2
      _ = (Fintype.card α : ℝ) := by simp
  unfold uniformMean
  constructor
  · exact div_nonneg hsum0 (le_of_lt hcard)
  · exact (div_le_iff₀ hcard).2 (by simpa using hsum1)

lemma uniformMean_bounds_with {α : Type*} (inst : Fintype α) [Nonempty α]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    0 ≤ @uniformMean α inst f ∧ @uniformMean α inst f ≤ 1 := by
  letI : Fintype α := inst
  exact uniformMean_bounds f hf

lemma uniformProb_bounds {α : Type*} [Fintype α] [Nonempty α] (P : α → Prop) :
    0 ≤ uniformProb P ∧ uniformProb P ≤ 1 := by
  unfold uniformProb
  apply uniformMean_bounds
  intro a
  exact indicator_bounds (P a)

lemma lowObservable_bounds {V : Type*} [Fintype V] [Nonempty V] [Nonempty (Pair V)]
    (q D : ℕ) (y : ℝ) (G : MGraph V) :
    0 ≤ lowObservable q D y G ∧ lowObservable q D y G ≤ 1 := by
  have hk : 0 ≤ lowKappa q D G ∧ lowKappa q D G ≤ 1 := by
    unfold lowKappa
    exact uniformProb_bounds _
  have hi := indicator_bounds (ENNReal.ofReal y < lifetime q G)
  unfold lowObservable
  constructor
  · exact mul_nonneg hk.1 hi.1
  · calc
      lowKappa q D G * indicator (ENNReal.ofReal y < lifetime q G) ≤ lowKappa q D G * 1 :=
        mul_le_mul_of_nonneg_left hi.2 hk.1
      _ ≤ 1 := by simpa using hk.2

lemma rootIndicator_bounds {V : Type*} [Fintype V] (q D : ℕ) (a : V)
    (G : MGraph V) :
    0 ≤ indicator (rootEvent q D a G) ∧ indicator (rootEvent q D a G) ≤ 1 :=
  indicator_bounds _

lemma finPair_nonempty (n : ℕ) (hn : 2 ≤ n) : Nonempty (Pair (Fin n)) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [a, b] at hv
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v h
  apply hab
  have he := Sym2.eq_iff.mp h
  rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ha.trans hb.symm
  · exact (hb.trans ha.symm).symm

lemma pmfMap_singleton_toReal {α β : Type*} [Nonempty α] [Fintype α]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β] [Nonempty β]
    (g : α → β) (b : β) :
    (PMF.map g (PMF.uniformOfFintype α) b).toReal =
      uniformMean (fun a => indicator (g a = b)) := by
  have h := lawMean_map_uniform g (fun x => indicator (x = b))
    ⟨1, fun x => by
      have hi := indicator_bounds (x = b)
      rcases hi with ⟨h0, h1⟩
      unfold indicator at *
      split_ifs <;> norm_num⟩
  have htsum :
      (∑' x, (PMF.map g (PMF.uniformOfFintype α) x).toReal * indicator (x = b)) =
        (PMF.map g (PMF.uniformOfFintype α) b).toReal := by
    simp [indicator]
  calc
    (PMF.map g (PMF.uniformOfFintype α) b).toReal =
        ∑' x, (PMF.map g (PMF.uniformOfFintype α) x).toReal * indicator (x = b) := htsum.symm
    _ = uniformMean (fun a => indicator (g a = b)) := by simpa using h

def canonicalTupleFintype (V : Type*) [Fintype V] (m : ℕ) : Fintype (EdgeTuple V m) :=
  @Pi.instFintype (Fin m) (fun _ => Pair V) (instDecidableEqFin m) (Fin.fintype m)
    (fun _ => @Subtype.fintype (Sym2 V) (fun e => ∀ v : V, e ≠ s(v, v))
      (fun e => Fintype.decidableForallFintype) Sym2.instFintype)

set_option maxHeartbeats 1000000 in
lemma tupleLaw_invariant {V : Type} [Fintype V] (m : ℕ)
    [Nonempty (EdgeTuple V m)]
    (hPre : PreRelabelStatement.{0, 0}) :
    invariantLaw (PMF.map tupleGraph
      (@PMF.uniformOfFintype (EdgeTuple V m) (canonicalTupleFintype V m)
        ‹Nonempty (EdgeTuple V m)›)) := by
  classical
  letI : Fintype (EdgeTuple V m) := canonicalTupleFintype V m
  letI : MeasurableSpace (EdgeTuple V m) := ⊤
  letI : MeasurableSingletonClass (EdgeTuple V m) := ⟨fun _ => by simp⟩
  let ν : PMF (MGraph V) := PMF.map tupleGraph
    (@PMF.uniformOfFintype (EdgeTuple V m) (canonicalTupleFintype V m)
      ‹Nonempty (EdgeTuple V m)›)
  intro π
  apply PMF.ext
  intro G
  have hleft : (ν.map (relabel π) G).toReal =
      graphMean m (fun H => indicator (relabel π H = G)) := by
    have h := pmfMap_singleton_toReal
      (g := fun x : EdgeTuple V m => relabel π (tupleGraph x)) G
    calc
      (ν.map (relabel π) G).toReal = uniformMean
          (fun x => indicator (relabel π (tupleGraph x) = G)) := by
        simpa [ν, PMF.map_comp, Function.comp_def] using h
      _ = graphMean m (fun H => indicator (relabel π H = G)) := by
        unfold graphMean
        rfl
  have hright : (ν G).toReal = graphMean m (fun H => indicator (H = G)) := by
    have h := pmfMap_singleton_toReal
      (g := fun x : EdgeTuple V m => tupleGraph x) G
    calc
      (ν G).toReal = uniformMean
          (fun x => indicator (tupleGraph x = G)) := by
        simpa [ν] using h
      _ = graphMean m (fun H => indicator (H = G)) := by
        unfold graphMean
        rfl
  rcases hPre V V π 0 (0 : MGraph V) with ⟨_, _, _, _, _, hmean⟩
  have hreal : (ν.map (relabel π) G).toReal = (ν G).toReal := by
    calc
      (ν.map (relabel π) G).toReal = graphMean m
          (fun H => indicator (relabel π H = G)) := hleft
      _ = graphMean m (fun H => indicator (H = G)) := hmean m (fun H => indicator (H = G))
      _ = (ν G).toReal := hright.symm
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp hreal with heq | ⟨_, htop⟩ | ⟨htop, _⟩
  · exact heq
  · exact False.elim ((PMF.apply_ne_top ν G) htop)
  · exact False.elim ((PMF.apply_ne_top (ν.map (relabel π)) G) htop)

set_option maxHeartbeats 1000000 in
theorem S5_34BStatement_of_deps
    (h31 : S5_31Statement) (h33B : S5_33BStatement) (h34A : S5_34AStatement)
    (hPreRelabel : PreRelabelStatement.{0, 0}) (hE01 : S5_E01Statement) :
    S5_34BStatement := by
  intro q n D hq hn hD hDn y hy a
  have hn2 : 2 ≤ n := by omega
  have hqN : 2 * q ≤ n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Pair (Fin n)) := finPair_nonempty n hn2
  let K : ℝ := (2 * n / ((n : ℝ) - 1)) * Real.sqrt ((1 + lifetimeConstant q) / y)
  have hK : 0 ≤ K := by
    have hden : 0 < (n : ℝ) - 1 := by
      have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      linarith
    unfold K
    apply mul_nonneg
    · exact div_nonneg (by positivity) (le_of_lt hden)
    · exact Real.sqrt_nonneg _
  let fLow : MGraph (Fin n) → ℝ := lowObservable q D y
  let fRoot : MGraph (Fin n) → ℝ := fun G => indicator (rootEvent q D a G)
  have hLowRange : ∀ G, 0 ≤ fLow G ∧ fLow G ≤ 1 := by
    intro G
    simpa [fLow] using lowObservable_bounds q D y G
  have hRootRange : ∀ G, 0 ≤ fRoot G ∧ fRoot G ≤ 1 := by
    intro G
    simpa [fRoot] using rootIndicator_bounds q D a G
  have hLowBound : ∃ C : ℝ, ∀ G, |fLow G| ≤ C := by
    refine ⟨1, fun G => ?_⟩
    exact abs_le.mpr ⟨by linarith [(hLowRange G).1], (hLowRange G).2⟩
  have hRootBound : ∃ C : ℝ, ∀ G, |fRoot G| ≤ C := by
    refine ⟨1, fun G => ?_⟩
    exact abs_le.mpr ⟨by linarith [(hRootRange G).1], (hRootRange G).2⟩
  have hLowMeanRange : ∀ m, 0 ≤ graphMean m fLow ∧ graphMean m fLow ≤ 1 := by
    intro m
    letI : Nonempty (EdgeTuple (Fin n) m) := ⟨fun _ => Classical.choice ‹Nonempty (Pair (Fin n))›⟩
    letI : Fintype (EdgeTuple (Fin n) m) := canonicalTupleFintype (Fin n) m
    unfold graphMean
    apply uniformMean_bounds_with
    intro x
    exact hLowRange (tupleGraph x)
  have hRootMeanRange : ∀ m, 0 ≤ graphMean m fRoot ∧ graphMean m fRoot ≤ 1 := by
    intro m
    letI : Nonempty (EdgeTuple (Fin n) m) := ⟨fun _ => Classical.choice ‹Nonempty (Pair (Fin n))›⟩
    letI : Fintype (EdgeTuple (Fin n) m) := canonicalTupleFintype (Fin n) m
    unfold graphMean
    apply uniformMean_bounds_with
    intro x
    exact hRootRange (tupleGraph x)
  have htime : ∀ t, 0 ≤ t → lowTime q n D y t ≤ K * rootProbability q D a t := by
    intro t ht
    rcases hE01.1 t ht with ⟨hweights, _, _, hbounded⟩
    have hLowSum : Summable (fun m => poissonWeight t m * graphMean m fLow) :=
      (hbounded 1 (fun m => graphMean m fLow) (by norm_num) hLowMeanRange).1
    have hRootScaledRange : ∀ m, 0 ≤ K * graphMean m fRoot ∧ K * graphMean m fRoot ≤ K := by
      intro m
      constructor
      · exact mul_nonneg hK (hRootMeanRange m).1
      · calc
          K * graphMean m fRoot ≤ K * 1 := mul_le_mul_of_nonneg_left (hRootMeanRange m).2 hK
          _ = K := by ring
    have hRootScaledSum : Summable
        (fun m => poissonWeight t m * (K * graphMean m fRoot)) :=
      (hbounded K (fun m => K * graphMean m fRoot) hK hRootScaledRange).1
    have hgraph : ∀ m, graphMean m fLow ≤ K * graphMean m fRoot := by
      intro m
      letI : Nonempty (EdgeTuple (Fin n) m) := ⟨fun _ => Classical.choice ‹Nonempty (Pair (Fin n))›⟩
      letI : MeasurableSpace (EdgeTuple (Fin n) m) := ⊤
      letI : MeasurableSingletonClass (EdgeTuple (Fin n) m) := ⟨fun _ => by simp⟩
      let edgeTupleFintype : Fintype (EdgeTuple (Fin n) m) := canonicalTupleFintype (Fin n) m
      letI : Fintype (EdgeTuple (Fin n) m) := edgeTupleFintype
      let ν : PMF (MGraph (Fin n)) :=
        PMF.map tupleGraph
          (@PMF.uniformOfFintype (EdgeTuple (Fin n) m) edgeTupleFintype
            ‹Nonempty (EdgeTuple (Fin n) m)›)
      have hνInv : invariantLaw ν := by
        simpa [ν] using tupleLaw_invariant (V := Fin n) m hPreRelabel
      have h2q : 2 * q ≤ Fintype.card (Fin n) := by simpa using hqN
      have hStatic := h31 (Fin n) q hq h2q D y hy ν hνInv a
      have hLowMap : lawMean ν fLow = graphMean m fLow := by
        calc
          lawMean ν fLow = @uniformMean (EdgeTuple (Fin n) m) edgeTupleFintype
              (fun x => fLow (tupleGraph x)) := by
            simpa [lawMean, ν] using
              lawMean_map_uniform
                (g := fun x : EdgeTuple (Fin n) m => tupleGraph x) fLow hLowBound
          _ = graphMean m fLow := by
            unfold graphMean
            rfl
      have hRootMap : lawMean ν fRoot = graphMean m fRoot := by
        calc
          lawMean ν fRoot = @uniformMean (EdgeTuple (Fin n) m) edgeTupleFintype
              (fun x => fRoot (tupleGraph x)) := by
            simpa [lawMean, ν] using
              lawMean_map_uniform
                (g := fun x : EdgeTuple (Fin n) m => tupleGraph x) fRoot hRootBound
          _ = graphMean m fRoot := by
            unfold graphMean
            rfl
      calc
        graphMean m fLow = lawMean ν fLow := hLowMap.symm
        _ ≤ (2 * Fintype.card (Fin n) / ((Fintype.card (Fin n) : ℝ) - 1)) *
            Real.sqrt ((1 + lifetimeConstant q) / y) * lawMean ν fRoot := hStatic.2.2
        _ = K * graphMean m fRoot := by simp [K, hRootMap, Fintype.card_fin]
    have hterm : ∀ m, poissonWeight t m * graphMean m fLow ≤
        poissonWeight t m * (K * graphMean m fRoot) := by
      intro m
      exact mul_le_mul_of_nonneg_left (hgraph m) (hweights m).1
    have hsum := hLowSum.tsum_le_tsum hterm hRootScaledSum
    have hfactor : (∑' m, poissonWeight t m * (K * graphMean m fRoot)) =
        K * (∑' m, poissonWeight t m * graphMean m fRoot) := by
      calc
        _ = ∑' m, K * (poissonWeight t m * graphMean m fRoot) := by
          congr 1
          funext m
          ring
        _ = _ := tsum_mul_left
    calc
      lowTime q n D y t = ∑' m, poissonWeight t m * graphMean m fLow := by
        rfl
      _ ≤ ∑' m, poissonWeight t m * (K * graphMean m fRoot) := hsum
      _ = K * rootProbability q D a t := by
        rw [hfactor]
        rfl
  have hlowInt : IntegrableOn (lowTime q n D y) (Set.Ici (0 : ℝ)) :=
    (h34A q n D hq hn y hy).2.2.1
  have hrootInt : IntegrableOn (rootProbability q D a) (Set.Ici (0 : ℝ)) :=
    (h33B q n D hq hn hD hDn a).1
  have hscaledInt : IntegrableOn (fun t => K * rootProbability q D a t) (Set.Ici (0 : ℝ)) :=
    hrootInt.const_mul K
  calc
    (∫ t in Set.Ici (0 : ℝ), lowTime q n D y t) ≤
        ∫ t in Set.Ici (0 : ℝ), K * rootProbability q D a t := by
      apply integral_mono_ae hlowInt hscaledInt
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t htmem
      exact htime t (Set.mem_Ici.mp htmem)
    _ = K * (∫ t in Set.Ici (0 : ℝ), rootProbability q D a t) := by
      rw [integral_const_mul]

end ThLean.W.S545

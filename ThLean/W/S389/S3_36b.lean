module

public import ThLean.BP.S3.Adapters

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S389
open ThresholdFoundations ThLean.BP.S3

private theorem pair_nonempty_of_card (V : Type u) [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  let a : V := Classical.choice inferInstance
  obtain ⟨b, hab⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) a
  refine ⟨⟨s(a,b), ?_⟩⟩
  intro v hv
  have hh := Sym2.eq_iff.mp hv
  rcases hh with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact hab (ha.trans hb.symm).symm
  · exact hab (ha.trans hb.symm).symm

private def prefixENNWeight {V : Type u} [Fintype V] (t : ℝ)
    (p : PoissonPrefix V) : ℝ≥0∞ :=
  ENNReal.ofReal (poissonWeight t p.1) / Fintype.card (EdgeTuple V p.1)

private theorem poissonGraphMeanENN_eq_prefix {V : Type u} [Fintype V]
    (t : ℝ) (h : MGraph V → ℝ≥0∞) :
    poissonGraphMeanENN t h =
      ∑' p : PoissonPrefix V, prefixENNWeight t p * h (tupleGraph p.2) := by
  unfold poissonGraphMeanENN poissonMixtureENN
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro m
  unfold prefixENNWeight uniformMeanENN
  rw [tsum_fintype]
  calc
    ENNReal.ofReal (poissonWeight t m) *
        ((∑ x : EdgeTuple V m, h (tupleGraph x)) / Fintype.card (EdgeTuple V m)) =
        (ENNReal.ofReal (poissonWeight t m) / Fintype.card (EdgeTuple V m)) *
          ∑ x : EdgeTuple V m, h (tupleGraph x) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ x : EdgeTuple V m,
        (ENNReal.ofReal (poissonWeight t m) / Fintype.card (EdgeTuple V m)) *
          h (tupleGraph x) := by rw [Finset.mul_sum]

private theorem poissonGraphMeanENN_eq_atoms {V : Type u} [Fintype V]
    (t : ℝ) (h : MGraph V → ℝ≥0∞) :
    poissonGraphMeanENN t h =
      ∑' G : MGraph V,
        (∑' p : (fun p : PoissonPrefix V => tupleGraph p.2) ⁻¹' {G},
          prefixENNWeight t p.1) * h G := by
  let state : PoissonPrefix V → MGraph V := fun p => tupleGraph p.2
  calc
    poissonGraphMeanENN t h =
        ∑' p : PoissonPrefix V, prefixENNWeight t p * h (state p) := by
          exact poissonGraphMeanENN_eq_prefix t h
    _ = ∑' G : MGraph V,
        ∑' p : state ⁻¹' {G}, prefixENNWeight t p.1 * h (state p.1) :=
          (ENNReal.tsum_fiberwise
            (fun p : PoissonPrefix V => prefixENNWeight t p * h (state p)) state).symm
    _ = ∑' G : MGraph V,
        (∑' p : state ⁻¹' {G}, prefixENNWeight t p.1) * h G := by
          apply tsum_congr
          intro G
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro p
          have hp := p.property
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
          simp [hp]

private theorem uniformIndicator_bounds {A : Type u} [Fintype A] [Nonempty A]
    (P : A → Prop) :
    0 ≤ uniformMean (fun a => indicator (P a)) ∧
      uniformMean (fun a => indicator (P a)) ≤ 1 := by
  have hc : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty A))
  unfold uniformMean indicator
  constructor
  · apply div_nonneg
    · exact Finset.sum_nonneg fun a ha => by split_ifs <;> norm_num
    · exact hc.le
  · rw [div_le_one hc]
    calc
      ∑ a : A, (if P a then (1 : ℝ) else 0) ≤ ∑ _a : A, (1 : ℝ) :=
        Finset.sum_le_sum fun a ha => by split_ifs <;> norm_num
      _ = (Fintype.card A : ℝ) := by simp

private theorem uniformMeanENN_ofReal {A : Type u} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    uniformMeanENN (fun a => ENNReal.ofReal (f a)) =
      ENNReal.ofReal (uniformMean f) := by
  have hc : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty A))
  unfold uniformMeanENN uniformMean
  rw [ENNReal.ofReal_div_of_pos hc]
  have hsum :
      ENNReal.ofReal (∑ a : A, f a) =
        ∑ a : A, ENNReal.ofReal (f a) := by
    have hh := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := f)
      (by intro a ha; exact hf a)
    simpa using hh
  rw [ENNReal.ofReal_natCast, ← hsum]

private theorem poissonGraphMeanENN_indicator_eq_ofReal {V : Type u} [Fintype V]
    (h31 : S3_31Statement) (hV : 2 ≤ Fintype.card V)
    (t : ℝ) (ht : 0 ≤ t) (G : MGraph V) :
    poissonGraphMeanENN t (fun H => ENNReal.ofReal (indicator (H = G))) =
      ENNReal.ofReal (poissonGraphMean t (fun H => indicator (H = G))) := by
  letI : Nonempty (Pair V) := pair_nonempty_of_card V hV
  have hp_nonneg : ∀ m, 0 ≤ poissonWeight t m := (h31 t ht).1
  have hp_summable : Summable (poissonWeight t) := (h31 t ht).2.1
  have q_nonneg (m : ℕ) :
      0 ≤ uniformMean (fun x : EdgeTuple V m => indicator (tupleGraph x = G)) := by
    letI : Nonempty (EdgeTuple V m) := ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair V))⟩
    exact (uniformIndicator_bounds (fun x : EdgeTuple V m => tupleGraph x = G)).1
  have q_le_one (m : ℕ) :
      uniformMean (fun x : EdgeTuple V m => indicator (tupleGraph x = G)) ≤ 1 := by
    letI : Nonempty (EdgeTuple V m) := ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair V))⟩
    exact (uniformIndicator_bounds (fun x : EdgeTuple V m => tupleGraph x = G)).2
  have hsum : Summable (fun m => poissonWeight t m *
      uniformMean (fun x : EdgeTuple V m => indicator (tupleGraph x = G))) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (hp_nonneg m) (q_nonneg m))
      (fun m => by
        calc
          poissonWeight t m * uniformMean (fun x : EdgeTuple V m =>
              indicator (tupleGraph x = G)) ≤ poissonWeight t m * 1 :=
            mul_le_mul_of_nonneg_left (q_le_one m) (hp_nonneg m)
          _ = poissonWeight t m := by ring)
      hp_summable
  rw [poissonGraphMeanENN, poissonGraphMean, poissonMixtureENN, poissonMixture]
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (hp_nonneg m) (q_nonneg m)) hsum]
  apply tsum_congr
  intro m
  letI : Nonempty (EdgeTuple V m) := ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair V))⟩
  have hqconv := uniformMeanENN_ofReal (A := EdgeTuple V m)
    (fun x => indicator (tupleGraph x = G))
    (fun x => by unfold indicator; split_ifs <;> norm_num)
  calc
    ENNReal.ofReal (poissonWeight t m) *
        uniformMeanENN (fun x : EdgeTuple V m =>
          ENNReal.ofReal (indicator (tupleGraph x = G))) =
        ENNReal.ofReal (poissonWeight t m) *
          ENNReal.ofReal (uniformMean (fun x : EdgeTuple V m =>
            indicator (tupleGraph x = G))) :=
          congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal (poissonWeight t m) * z) hqconv
    _ = ENNReal.ofReal (poissonWeight t m *
        uniformMean (fun x : EdgeTuple V m => indicator (tupleGraph x = G))) := by
          exact (ENNReal.ofReal_mul (hp_nonneg m)).symm

private theorem looplessRate_eq_pairRate {V : Type u} [Fintype V]
    (t : ℝ) : pairRate (V := V) (t / (Fintype.card (Pair V) : ℝ)) =
      looplessRate (V := V) t := by
  funext e
  by_cases hd : ∃ v : V, e = s(v,v)
  · have hn : e ∉ completeEdges (V := V) := by
      intro he
      have hno := (Finset.mem_filter.mp he).2
      rcases hd with ⟨v,hv⟩
      exact hno v hv
    simp [pairRate, looplessRate, hd, hn]
  · have hc : e ∈ completeEdges (V := V) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro v hv
      exact hd ⟨v, hv⟩
    simp [pairRate, looplessRate, hd, hc]

theorem S3_36bStatement_of_deps
    (h31 : S3_31Statement) (h36 : S3_36Statement.{u}) :
    S3_36bStatement.{u} := by
  intro V _ hV t h ht
  let state : PoissonPrefix V → MGraph V := fun p => tupleGraph p.2
  have hAtom (G : MGraph V) :
      (∑' p : state ⁻¹' {G}, prefixENNWeight t p.1) =
        ENNReal.ofReal (independentPoissonGraphMass (looplessRate t) G) := by
    let test : MGraph V → ℝ≥0∞ := fun H => ENNReal.ofReal (indicator (H = G))
    have hdecomp := poissonGraphMeanENN_eq_atoms t test
    have hsingleton :
          (∑' K : MGraph V,
          (∑' p : state ⁻¹' {K}, prefixENNWeight t p.1) * test K) =
          (∑' p : state ⁻¹' {G}, prefixENNWeight t p.1) := by
      rw [tsum_eq_single G]
      · simp [test, indicator]
      · intro K hKG
        simp [test, indicator, hKG]
    calc
      (∑' p : state ⁻¹' {G}, prefixENNWeight t p.1) =
          poissonGraphMeanENN t test := by
            rw [hdecomp]
            exact hsingleton.symm
      _ = ENNReal.ofReal (poissonGraphMean t (fun H => indicator (H = G))) :=
            poissonGraphMeanENN_indicator_eq_ofReal h31 hV t ht G
      _ = ENNReal.ofReal (independentPoissonGraphMass (looplessRate t) G) := by
            congr 1
            have h36G := (h36 V hV).1 t G ht
            rw [looplessRate_eq_pairRate (V := V) t] at h36G
            exact h36G
  calc
    poissonGraphMeanENN t h =
        ∑' G : MGraph V,
          (∑' p : state ⁻¹' {G}, prefixENNWeight t p.1) * h G := by
            exact poissonGraphMeanENN_eq_atoms t h
    _ = independentPoissonGraphMeanENN (looplessRate t) h := by
          unfold independentPoissonGraphMeanENN
          apply tsum_congr
          intro G
          rw [hAtom G]

end ThLean.W.S389

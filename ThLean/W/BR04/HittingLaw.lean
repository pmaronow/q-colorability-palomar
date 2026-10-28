import ThLean.Defs

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
open ThresholdFoundations
namespace ThLean.W.BR04

private lemma uniformMean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  unfold uniformMean
  simp [Fintype.card_ne_zero]

private lemma uniformMean_mono {A : Type*} [Fintype A] [Nonempty A]
    {f g : A → ℝ} (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < (Fintype.card A : ℝ))).2
  exact Finset.sum_le_sum fun a _ => h a

private lemma uniformMean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : uniformMean (f ∘ e) = uniformMean f := by
  unfold uniformMean
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

private lemma uniformMean_fintype_irrel {A : Type*} (i j : Fintype A) (f : A → ℝ) :
    @uniformMean A i f = @uniformMean A j f := by
  have h : i = j := Subsingleton.elim i j
  rw [h]

private lemma uniformMean_prod {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a, b))) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [Nat.cast_mul]
  conv_lhs => rw [Finset.sum_div]
  conv_rhs => rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b : B, f (a, b)) / ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) =
      ((∑ b : B, f (a, b)) / (Fintype.card B : ℝ)) / (Fintype.card A : ℝ) := by
        rw [div_div, mul_comm]

private lemma uniformMean_snd {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : B → ℝ) :
    uniformMean (fun p : A × B => f p.2) = uniformMean f := by
  rw [uniformMean_prod]
  simp only [uniformMean_const]

private lemma uniformMean_snd_explicit {A B : Type*}
    (iAB : Fintype (A × B)) (iA : Fintype A) (iB : Fintype B)
    [Nonempty A] [Nonempty B] (f : B → ℝ) :
    @uniformMean (A × B) iAB (fun p => f p.2) = @uniformMean B iB f := by
  letI := iA
  letI := iB
  let instProd : Fintype (A × B) := inferInstance
  have hprod : iAB = instProd := Subsingleton.elim _ _
  rw [hprod]
  calc
    @uniformMean (A × B) instProd (fun p => f p.2) =
        @uniformMean (A × B) (instFintypeProd A B) (fun p => f p.2) :=
          uniformMean_fintype_irrel instProd (instFintypeProd A B) _
    _ = @uniformMean B iB f := uniformMean_snd (A := A) (B := B) f

private lemma uniformProb_bounds {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) : 0 ≤ uniformProb P ∧ uniformProb P ≤ 1 := by
  unfold uniformProb
  constructor
  · calc
      0 = uniformMean (fun _ : A => (0 : ℝ)) := (uniformMean_const 0).symm
      _ ≤ uniformMean (fun a => indicator (P a)) :=
        uniformMean_mono (by intro a; unfold indicator; split_ifs <;> norm_num)
  · calc
      uniformMean (fun a => indicator (P a)) ≤ uniformMean (fun _ : A => (1 : ℝ)) :=
        uniformMean_mono (by intro a; unfold indicator; split_ifs <;> norm_num)
      _ = 1 := uniformMean_const 1

private lemma uniformProb_bounds_explicit {A : Type*} (inst : Fintype A)
    [Nonempty A] (P : A → Prop) :
    @uniformProb A inst P ≥ 0 ∧ @uniformProb A inst P ≤ 1 := by
  letI := inst
  exact uniformProb_bounds P

private lemma indicator_mono {P Q : Prop} (h : P → Q) : indicator P ≤ indicator Q := by
  by_cases hp : P
  · simp [indicator, hp, h hp]
  · simp [indicator, hp]
    split_ifs <;> norm_num

private lemma pair_nonempty {n : ℕ} (hn : 2 ≤ n) : Nonempty (Pair (Fin n)) := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  refine ⟨⟨s(z, o), ?_⟩⟩
  intro v hv
  simp only [Sym2.eq_iff] at hv
  have hzo : z ≠ o := by
    intro he
    have hval := congrArg Fin.val he
    norm_num at hval
  rcases hv with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact hzo (h0.trans h1.symm)
  · exact hzo (h0.trans h1.symm)

private lemma colorable_of_subgraph {V : Type*} {q : ℕ} {G G' : MGraph V}
    (hsub : subgraph G G') (hc : Colorable q G') : Colorable q G := by
  rcases hc with ⟨σ, hσ⟩
  exact ⟨σ, fun u v huv => hσ u v (lt_of_lt_of_le huv (hsub (s(u, v))))⟩

private lemma zero_add_mgraph {V : Type*} (G : MGraph V) :
    (0 : MGraph V) + G = G := by
  funext e
  simp

private lemma snoc_prefix_subgraph {V : Type*} [Fintype V] {k : ℕ}
    (x : EdgeTuple V k) (e : Pair V) :
    subgraph (tupleGraph x) (tupleGraph (Fin.snoc (α := fun _ : Fin (k + 1) => Pair V) x e)) := by
  intro a
  change (Finset.univ.filter (fun i : Fin k => (x i).val = a)).card ≤
    (Finset.univ.filter (fun i : Fin (k + 1) =>
      (Fin.snoc (α := fun _ : Fin (k + 1) => Pair V) x e i).val = a)).card
  refine Finset.card_le_card_of_injOn Fin.castSucc ?_ ?_
  · intro i hi
    have hp : (x i).val = a := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    constructor
    · simp
    · simpa only [Fin.snoc_castSucc] using hp
  · intro i hi j hj hij
    exact (Fin.castSucc_injective k) hij

private lemma processSurvival_bounds {n q : ℕ} (hn : 2 ≤ n) :
    ∀ m, 0 ≤ processSurvival (V := Fin n) q m ∧ processSurvival (V := Fin n) q m ≤ 1 := by
  intro m
  letI : Nonempty (Pair (Fin n)) := pair_nonempty hn
  unfold processSurvival survival
  apply uniformProb_bounds_explicit

private lemma processSurvival_step {n q : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    processSurvival (V := Fin n) q (m + 1) ≤ processSurvival (V := Fin n) q m := by
  letI : Nonempty (Pair (Fin n)) := pair_nonempty hn
  let e : EdgeTuple (Fin n) (m + 1) ≃ Pair (Fin n) × EdgeTuple (Fin n) m :=
    { toFun := fun x => (x (Fin.last m), Fin.init x)
      invFun := fun z => Fin.snoc
        (α := fun _ : Fin (m + 1) => Pair (Fin n)) z.2 z.1
      left_inv := fun x => Fin.snoc_init_self x
      right_inv := by
        rintro ⟨a, x⟩
        simp [Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc] }
  let g : Pair (Fin n) × EdgeTuple (Fin n) m → ℝ := fun z =>
    indicator (Colorable q (tupleGraph
      (Fin.snoc (α := fun _ : Fin (m + 1) => Pair (Fin n)) z.2 z.1)))
  have hcomp : (fun x : EdgeTuple (Fin n) (m + 1) =>
      indicator (Colorable q (tupleGraph x))) = g ∘ e := by
    funext x
    simp only [Function.comp_apply]
    change indicator (Colorable q (tupleGraph x)) =
      indicator (Colorable q (tupleGraph
        (Fin.snoc (α := fun _ : Fin (m + 1) => Pair (Fin n)) (Fin.init x) (x (Fin.last m)))) )
    rw [Fin.snoc_init_self]
  have hreindex : uniformMean (fun x : EdgeTuple (Fin n) (m + 1) =>
      indicator (Colorable q (tupleGraph x))) = uniformMean g :=
    (congrArg uniformMean hcomp).trans (uniformMean_equiv e g)
  calc
    processSurvival (V := Fin n) q (m + 1) = uniformMean g := by
      calc
        processSurvival (V := Fin n) q (m + 1) =
            uniformMean (fun x : EdgeTuple (Fin n) (m + 1) =>
              indicator (Colorable q (tupleGraph x))) := by
                simp [processSurvival, survival, uniformProb, Pi.add_apply, zero_add]
                exact uniformMean_fintype_irrel _ _ _
        _ = uniformMean g := hreindex
    _ ≤ uniformMean (fun z : Pair (Fin n) × EdgeTuple (Fin n) m =>
          indicator (Colorable q (tupleGraph z.2))) := by
            apply uniformMean_mono
            intro z
            exact indicator_mono (colorable_of_subgraph (snoc_prefix_subgraph z.2 z.1))
    _ = processSurvival (V := Fin n) q m := by
          calc
            uniformMean (fun z : Pair (Fin n) × EdgeTuple (Fin n) m =>
                indicator (Colorable q (tupleGraph z.2))) =
              uniformMean (fun x : EdgeTuple (Fin n) m =>
                indicator (Colorable q (tupleGraph x))) :=
                  uniformMean_snd (A := Pair (Fin n)) (B := EdgeTuple (Fin n) m)
                    (fun x => indicator (Colorable q (tupleGraph x)))
            _ = processSurvival (V := Fin n) q m := by
                  simp [processSurvival, survival, uniformProb, Pi.add_apply, zero_add]
                  exact uniformMean_fintype_irrel _ _ _

private lemma processSurvival_antitone {n q : ℕ} (hn : 2 ≤ n) :
    Antitone (processSurvival (V := Fin n) q) :=
  antitone_nat_of_succ_le fun m => processSurvival_step hn m

private lemma processSurvival_tendsto_inf {n q : ℕ} (hn : 2 ≤ n) :
    Tendsto (processSurvival (V := Fin n) q) atTop
      (𝓝 (infiniteHittingProbability (V := Fin n) q)) := by
  let S := processSurvival (V := Fin n) q
  have hb : BddBelow (Set.range S) := by
    refine ⟨0, ?_⟩
    rintro y ⟨m, rfl⟩
    exact (processSurvival_bounds hn m).1
  have hnemp : (Set.range S).Nonempty := ⟨S 0, ⟨0, rfl⟩⟩
  have hlim : Tendsto S atTop (𝓝 (sInf (Set.range S))) :=
    tendsto_atTop_isGLB (processSurvival_antitone hn) (isGLB_csInf hnemp hb)
  simpa [S, infiniteHittingProbability] using hlim

private lemma processSurvival_inf_bounds {n q : ℕ} (hn : 2 ≤ n) :
    0 ≤ infiniteHittingProbability (V := Fin n) q ∧
    infiniteHittingProbability (V := Fin n) q ≤ 1 := by
  let S := processSurvival (V := Fin n) q
  have hlow : ∀ y ∈ Set.range S, 0 ≤ y := by
    rintro y ⟨m, rfl⟩
    exact (processSurvival_bounds hn m).1
  have hne : (Set.range S).Nonempty := ⟨S 0, ⟨0, rfl⟩⟩
  have hb : BddBelow (Set.range S) := ⟨0, hlow⟩
  have h₀ : 0 ≤ sInf (Set.range S) := le_csInf hne hlow
  have h₁ : sInf (Set.range S) ≤ 1 :=
    (csInf_le hb ⟨0, rfl⟩).trans (processSurvival_bounds hn 0).2
  simpa [infiniteHittingProbability] using And.intro h₀ h₁

private lemma hittingMass_nonneg {n q : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    0 ≤ hittingMass (V := Fin n) q k := by
  unfold hittingMass
  exact sub_nonneg.mpr (processSurvival_step hn k)

private lemma hittingMass_partial_sum {n q m N : ℕ} :
    (∑ k ∈ Finset.range N, hittingMass (V := Fin n) q (m + k)) =
      processSurvival (V := Fin n) q m - processSurvival (V := Fin n) q (m + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [hittingMass]
      rw [Nat.add_assoc]
      ring

private lemma hittingMass_tail_sum {n q : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    ∑' k : ℕ, ENNReal.ofReal (hittingMass (V := Fin n) q (m + k)) =
      ENNReal.ofReal (processSurvival (V := Fin n) q m -
        infiniteHittingProbability (V := Fin n) q) := by
  let f : ℕ → ℝ := fun k => hittingMass (V := Fin n) q (m + k)
  have hf : ∀ k, 0 ≤ f k := fun k => hittingMass_nonneg hn (m + k)
  have hseq : Tendsto (fun k => processSurvival (V := Fin n) q (m + k)) atTop
      (𝓝 (infiniteHittingProbability (V := Fin n) q)) := by
    convert (processSurvival_tendsto_inf hn).comp (tendsto_add_atTop_nat m) using 1 <;>
      simp [Function.comp_def, Nat.add_comm]
  have hpartial : ∀ N, (∑ k ∈ Finset.range N, f k) =
      processSurvival (V := Fin n) q m - processSurvival (V := Fin n) q (m + N) := by
    intro N
    simpa [f] using (hittingMass_partial_sum (n := n) (q := q) (m := m) (N := N))
  have hsum : HasSum f (processSurvival (V := Fin n) q m -
      infiniteHittingProbability (V := Fin n) q) :=
    (hasSum_iff_tendsto_nat_of_nonneg hf _).2 (by
      convert (tendsto_const_nhds.sub hseq) using 1
      funext N
      exact hpartial N)
  have hreal : (∑' k, f k) = processSurvival (V := Fin n) q m -
      infiniteHittingProbability (V := Fin n) q := hsum.tsum_eq
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hsum.summable, hreal]

private lemma hittingMass_law {n q : ℕ} (hq : 0 < q) (hn : 2 ≤ n) :
    (∀ k : ℕ, 0 ≤ hittingMass (V := Fin n) q k) ∧
    (0 ≤ infiniteHittingProbability (V := Fin n) q ∧
      infiniteHittingProbability (V := Fin n) q ≤ 1) ∧
    ((∑' k : ℕ, ENNReal.ofReal (hittingMass (V := Fin n) q k)) +
      ENNReal.ofReal (infiniteHittingProbability (V := Fin n) q) = 1) ∧
    (∀ m : ℕ, ENNReal.ofReal (processSurvival (V := Fin n) q m) =
      ENNReal.ofReal (infiniteHittingProbability (V := Fin n) q) +
        ∑' k : ℕ, ENNReal.ofReal (hittingMass (V := Fin n) q (m+k))) := by
  have hmass : ∀ k : ℕ, 0 ≤ hittingMass (V := Fin n) q k := hittingMass_nonneg hn
  have hinf := processSurvival_inf_bounds (n := n) (q := q) hn
  have hzero : processSurvival (V := Fin n) q 0 = 1 :=
    ThresholdFoundations.Sanity.processSurvival_zero (V := Fin n) (q := q) hq
  refine ⟨hmass, hinf, ?_, ?_⟩
  · have htail : (∑' k : ℕ, ENNReal.ofReal (hittingMass (V := Fin n) q k)) =
        ENNReal.ofReal (1 - infiniteHittingProbability (V := Fin n) q) := by
      simpa [hzero] using (hittingMass_tail_sum (n := n) (q := q) hn 0)
    calc
      (∑' k : ℕ, ENNReal.ofReal (hittingMass (V := Fin n) q k)) +
          ENNReal.ofReal (infiniteHittingProbability (V := Fin n) q) =
        ENNReal.ofReal (1 - infiniteHittingProbability (V := Fin n) q) +
          ENNReal.ofReal (infiniteHittingProbability (V := Fin n) q) := by rw [htail]
      _ = 1 := by
        rw [← ENNReal.ofReal_add (sub_nonneg.mpr hinf.2) hinf.1]
        congr 1
        ring
        norm_num
  · intro m
    have htail := hittingMass_tail_sum (n := n) (q := q) hn m
    have hbelow : BddBelow (Set.range (processSurvival (V := Fin n) q)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨j, rfl⟩
      exact (processSurvival_bounds hn j).1
    have hle : infiniteHittingProbability (V := Fin n) q ≤
        processSurvival (V := Fin n) q m := by
      exact csInf_le hbelow ⟨m, rfl⟩
    calc
      ENNReal.ofReal (processSurvival (V := Fin n) q m) =
          ENNReal.ofReal (infiniteHittingProbability (V := Fin n) q +
            (processSurvival (V := Fin n) q m - infiniteHittingProbability (V := Fin n) q)) := by
              congr 1
              ring
      _ = ENNReal.ofReal (infiniteHittingProbability (V := Fin n) q) +
            ENNReal.ofReal (processSurvival (V := Fin n) q m -
              infiniteHittingProbability (V := Fin n) q) := by
              rw [ENNReal.ofReal_add hinf.1 (sub_nonneg.mpr hle)]
      _ = ENNReal.ofReal (infiniteHittingProbability (V := Fin n) q) +
            ∑' k : ℕ, ENNReal.ofReal (hittingMass (V := Fin n) q (m+k)) := by
              rw [htail]

theorem HittingLawStatement_of_deps (hpre : PreLifetimeStatement.{0}) : HittingLawStatement := by
  intro q n hq hn
  letI : Nonempty (Pair (Fin n)) := pair_nonempty hn
  have hbase := hittingMass_law (n := n) (q := q) (by omega) hn
  have hlast : 2*q ≤ n → infiniteHittingProbability (V := Fin n) q = 0 := by
    intro hqN
    have hpreN := hpre (V := Fin n) q hq (by simpa using hn)
    have hG := hpreN.1 (0 : MGraph (Fin n)) (by intro v; simp [Loopless])
    have hsum : Summable (survival (V := Fin n) q (0 : MGraph (Fin n))) :=
      (hG.2.2.2.2 (by simpa [Fintype.card_fin] using hqN)).2.2.1
    have hzero : Tendsto (processSurvival (V := Fin n) q) atTop (𝓝 0) := by
      change Tendsto (fun m => survival (V := Fin n) q (0 : MGraph (Fin n)) m) atTop (𝓝 0)
      exact hsum.tendsto_atTop_zero
    exact tendsto_nhds_unique (processSurvival_tendsto_inf hn) hzero
  exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2, hlast⟩

end ThLean.W.BR04

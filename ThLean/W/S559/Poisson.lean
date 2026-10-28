import ThLean.BP.S5.Poisson
import ThLean.Contrib.S559.Hazard

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S559
open ThresholdFoundations ThLean.BP.S5

private lemma uniformMean_nonneg_of_nonneg {α : Type*} [Fintype α]
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ uniformMean f := by
  unfold uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => hf x
  · exact Nat.cast_nonneg _

private lemma uniformMean_le_one_of_le_one {α : Type*} [Fintype α]
    (f : α → ℝ) (hf : ∀ x, f x ≤ 1) : uniformMean f ≤ 1 := by
  unfold uniformMean
  have hs : (∑ x, f x) ≤ (Fintype.card α : ℝ) := by
    calc
      (∑ x, f x) ≤ ∑ _x : α, (1 : ℝ) := Finset.sum_le_sum fun x _ => hf x
      _ = (Fintype.card α : ℝ) := by simp
  by_cases hc : Fintype.card α = 0
  · simp [hc] at hs ⊢
  · have hp : 0 < (Fintype.card α : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
    exact (div_le_iff₀ hp).2 (by simpa using hs)

private lemma uniformMean_bounds_of_bounds {α : Type*} [Fintype α]
    (f : α → ℝ) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 :=
  ⟨uniformMean_nonneg_of_nonneg f h0, uniformMean_le_one_of_le_one f h1⟩

private lemma indicator_bounds (P : Prop) : 0 ≤ indicator P ∧ indicator P ≤ 1 := by
  by_cases hP : P <;> simp [indicator, hP]

private lemma poissonGraphMean_bounds (hE01 : S5_E01Statement)
    {V : Type*} [Fintype V] (t : ℝ) (ht : 0 ≤ t) (f : MGraph V → ℝ)
    (hf : ∀ G, 0 ≤ f G ∧ f G ≤ 1) :
    0 ≤ poissonGraphMean t f ∧ poissonGraphMean t f ≤ 1 := by
  let b : ℕ → ℝ := fun m => uniformMean (fun x : EdgeTuple V m => f (tupleGraph x))
  have hb : ∀ m, 0 ≤ b m ∧ b m ≤ 1 := by
    intro m
    exact uniformMean_bounds_of_bounds _ (fun x => (hf (tupleGraph x)).1)
      (fun x => (hf (tupleGraph x)).2)
  have hm := (hE01.1 t ht).2.2.2 1 b (by norm_num) hb
  simpa [poissonGraphMean, b, poissonMixture] using hm.2

private lemma countMean_eq_poissonGraphMean {V : Type} [Fintype V]
    (h08B : S5_08BStatement) (hV : 2 ≤ Fintype.card V)
    (r : ℝ) (hr : 0 ≤ r) (f : MGraph V → ℝ) (hf : ∃ C : ℝ, ∀ G, |f G| ≤ C) :
    countMean r f = poissonGraphMean (r * ((Fintype.card V).choose 2 : ℝ)) f := by
  have hchoose : 0 < ((Fintype.card V).choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ Fintype.card V)
  have h := h08B V hV (r * ((Fintype.card V).choose 2 : ℝ)) (by positivity) f hf
  have hdiv : (r * ((Fintype.card V).choose 2 : ℝ)) /
      ((Fintype.card V).choose 2 : ℝ) = r := by
    field_simp
  rw [hdiv] at h
  exact h.symm

private lemma countMean_bounds (hE01 : S5_E01Statement) (h08B : S5_08BStatement)
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (r : ℝ) (hr : 0 ≤ r) (f : MGraph V → ℝ)
    (hf : ∀ G, 0 ≤ f G ∧ f G ≤ 1) :
    0 ≤ countMean r f ∧ countMean r f ≤ 1 := by
  have hbounded : ∃ C : ℝ, ∀ G, |f G| ≤ C := ⟨1, fun G => by
    rcases hf G with ⟨h0, h1⟩
    rw [abs_le]
    exact ⟨by linarith, h1⟩⟩
  rw [countMean_eq_poissonGraphMean h08B hV r hr f hbounded]
  exact poissonGraphMean_bounds hE01 (r * ((Fintype.card V).choose 2 : ℝ))
    (by positivity) f hf

private lemma pair_nonempty_of_card_two {V : Type} [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  have hex : ∃ a b : V, a ≠ b := by
    by_contra h
    have heq : ∀ a b : V, a = b := by
      intro a b
      by_contra hab
      exact h ⟨a, b, hab⟩
    have hc : Fintype.card V ≤ 1 := (Fintype.card_le_one_iff).2 heq
    omega
  obtain ⟨a, b, hab⟩ := hex
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hv
  have hcases := (Sym2.eq_iff).1 hv
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst_vars <;> exact hab rfl

private lemma poissonGraphMean_fin_sum (hE01 : S5_E01Statement) (hE08 : S5_E08Statement)
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (t : ℝ) (ht : 0 ≤ t) (j : ℕ) (f : Fin j → MGraph V → ℝ)
    (hf : ∀ i G, 0 ≤ f i G ∧ f i G ≤ 1) :
    poissonGraphMean t (fun G => ∑ i : Fin j, f i G) =
      ∑ i : Fin j, poissonGraphMean t (f i) := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  letI : Nonempty (Pair V) := pair_nonempty_of_card_two hV
  have htuple : ∀ m : ℕ, Nonempty (EdgeTuple V m) := by
    intro m
    exact ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair V))⟩
  have hsummable : ∀ i : Fin j, Summable (fun m : ℕ =>
      poissonWeight t m * uniformMean (fun x : EdgeTuple V m => f i (tupleGraph x))) := by
    intro i
    let b : ℕ → ℝ := fun m => uniformMean (fun x : EdgeTuple V m => f i (tupleGraph x))
    have hb : ∀ m, 0 ≤ b m ∧ b m ≤ 1 := by
      intro m
      exact uniformMean_bounds_of_bounds _ (fun x => (hf i (tupleGraph x)).1)
        (fun x => (hf i (tupleGraph x)).2)
    exact ((hE01.1 t ht).2.2.2 1 b (by norm_num) hb).1
  have hcomm := Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun i : Fin j => fun m : ℕ => poissonWeight t m *
      uniformMean (fun x : EdgeTuple V m => f i (tupleGraph x)))
    (fun i _ => hsummable i)
  unfold poissonGraphMean poissonMixture
  rw [← hcomm]
  apply tsum_congr
  intro m
  have hmean := hE08.2.2 (EdgeTuple V m) (Fin j)
    (fun i x => f i (tupleGraph x))
  simpa [Finset.mul_sum] using congrArg (fun z : ℝ => poissonWeight t m * z) hmean

private lemma increment_bounds {V : Type} [Fintype V]
    (q : ℕ) (B : MGraph V) (j : ℕ) :
    0 ≤ increment q B j ∧ increment q B j ≤ 1 := by
  unfold increment
  exact uniformMean_bounds_of_bounds _ (fun _ => (indicator_bounds _).1)
    (fun _ => (indicator_bounds _).2)

private lemma blocking_bounds {V : Type} [Fintype V]
    (q : ℕ) (B : MGraph V) (j : ℕ) :
    0 ≤ blocking q B j ∧ blocking q B j ≤ 1 := by
  unfold blocking listMean
  exact uniformMean_bounds_of_bounds _ (fun _ => (indicator_bounds _).1)
    (fun _ => (indicator_bounds _).2)

private lemma tupleGraph_loopless {V : Type} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) : Loopless (tupleGraph x) := by
  intro v
  unfold tupleGraph
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have he : (x i).val = s(v, v) := (Finset.mem_filter.mp hi).2
  exact (x i).property v he

private lemma blocking_prefix_identity (h13 : S5_13Statement)
    {V : Type} [Fintype V] [Nonempty V] (q : ℕ) (hq : 3 ≤ q)
    (B : MGraph V) (hB : Loopless B) (j : ℕ) :
    blocking q B j = ∑ i ∈ Finset.range j, increment q B i := by
  rcases h13 V q hq B hB with ⟨_, hrest⟩
  rcases hrest j with ⟨_, _, _, _, hsum, _⟩
  exact hsum

theorem S5_15B_first_three_of_deps (h13 : S5_13Statement)
    (_h15A : S5_15AStatement) (_h12 : S5_12Statement) (h08B : S5_08BStatement)
    (hE01 : S5_E01Statement) (hE08 : S5_E08Statement) :
    ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
    ∀ rate s : ℝ, 0 < rate → 0 ≤ s →
      (∀ j, 0 ≤ incrementMean (V := V) q (rate * s) j) ∧
      (∀ j, 0 ≤ blockingMean (V := V) q (rate * s) j ∧
        blockingMean (V := V) q (rate * s) j ≤ 1) ∧
      (∀ j, blockingMean (V := V) q (rate * s) j =
        ∑ i ∈ Finset.range j, incrementMean (V := V) q (rate * s) i) := by
  intro V _ q hq hV rate s hrate hs
  let r : ℝ := rate * s
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hnonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  letI : Nonempty V := hnonempty
  constructor
  · intro j
    have h := countMean_bounds hE01 h08B hV r hr (increment q · j)
      (fun B => increment_bounds q B j)
    simpa [incrementMean, r] using h.1
  constructor
  · intro j
    have h := countMean_bounds hE01 h08B hV r hr (blocking q · j)
      (fun B => blocking_bounds q B j)
    simpa [blockingMean, r] using h
  · intro j
    let f : Fin j → MGraph V → ℝ := fun i B => increment q B i.val
    have hbound : ∀ i G, 0 ≤ f i G ∧ f i G ≤ 1 := by
      intro i G
      exact increment_bounds q G i.val
    have hpgEq : poissonGraphMean (r * ((Fintype.card V).choose 2 : ℝ))
        (fun B : MGraph V => blocking q B j) =
        poissonGraphMean (r * ((Fintype.card V).choose 2 : ℝ))
          (fun B => ∑ i : Fin j, f i B) := by
      unfold poissonGraphMean poissonMixture
      apply tsum_congr
      intro m
      change poissonWeight (r * ((Fintype.card V).choose 2 : ℝ)) m *
          ((∑ x : EdgeTuple V m, blocking q (tupleGraph x) j) /
            (Fintype.card (EdgeTuple V m) : ℝ)) =
        poissonWeight (r * ((Fintype.card V).choose 2 : ℝ)) m *
          ((∑ x : EdgeTuple V m, ∑ i : Fin j, f i (tupleGraph x)) /
            (Fintype.card (EdgeTuple V m) : ℝ))
      apply congrArg (fun z : ℝ => poissonWeight (r * ((Fintype.card V).choose 2 : ℝ)) m *
        (z / (Fintype.card (EdgeTuple V m) : ℝ)))
      apply Finset.sum_congr rfl
      intro x hx
      have hp := blocking_prefix_identity h13 q hq (tupleGraph x)
        (tupleGraph_loopless x) j
      simpa [f, Fin.sum_univ_eq_sum_range] using hp
    have hlin := poissonGraphMean_fin_sum hE01 hE08 hV
      (r * ((Fintype.card V).choose 2 : ℝ)) (by positivity) j f hbound
    have hpg := hpgEq.trans hlin
    have hleft := countMean_eq_poissonGraphMean h08B hV r hr
      (fun B : MGraph V => blocking q B j) ⟨1, fun B => by
        rcases blocking_bounds q B j with ⟨h0, h1⟩
        rw [abs_le]
        exact ⟨by linarith, h1⟩⟩
    change countMean r (blocking q · j) =
      ∑ i ∈ Finset.range j, countMean r (increment q · i)
    rw [hleft]
    rw [hpg]
    change (∑ i : Fin j, poissonGraphMean
        (r * ((Fintype.card V).choose 2 : ℝ))
        (fun B : MGraph V => increment q B i.val)) =
      ∑ i ∈ Finset.range j, countMean r (fun B : MGraph V => increment q B i)
    rw [Fin.sum_univ_eq_sum_range (fun k => poissonGraphMean
      (r * ((Fintype.card V).choose 2 : ℝ)) (fun B : MGraph V => increment q B k))]
    apply Finset.sum_congr rfl
    intro i hi
    have hmi := countMean_eq_poissonGraphMean h08B hV r hr
      (fun B : MGraph V => increment q B i) ⟨1, fun B => by
        rcases increment_bounds q B i with ⟨h0, h1⟩
        rw [abs_le]
        exact ⟨by linarith, h1⟩⟩
    simpa [f] using hmi.symm

theorem S5_15BStatement_from_deps_and_hazard (h13 : S5_13Statement)
    (h15A : S5_15AStatement) (h12 : S5_12Statement) (h08B : S5_08BStatement)
    (hE01 : S5_E01Statement) (hE08 : S5_E08Statement)
    (hhazard : ThLean.Contrib.S559.S5_15BHazardStatement) :
    ThLean.BP.S5.S5_15BStatement := by
  intro V _ q hq hV rate s hrate hs
  rcases S5_15B_first_three_of_deps h13 h15A h12 h08B hE01 hE08
      V q hq hV rate s hrate hs with ⟨hi, hb, hsum⟩
  exact ⟨hi, hb, hsum, hhazard V q hq hV rate s hrate hs⟩

end ThLean.W.S559

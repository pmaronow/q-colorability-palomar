import ThLean.BP.S4.Bridges

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S436S
open ThresholdFoundations

private theorem indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split <;> norm_num

private theorem uniformProb_nonneg {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProb P := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => indicator_nonneg _) (Nat.cast_nonneg _)

private theorem uniformProb_eq_card {A : Type*} [Fintype A] (P : A → Prop) :
    uniformProb P = (Nat.card {a // P a} : ℝ) / Fintype.card A := by
  simp [Nat.card_eq_fintype_card, uniformProb, uniformMean, indicator,
    Fintype.card_subtype, Finset.sum_boole]

private theorem avoid_probability {A : Type*} [Fintype A] (a : A) (k : ℕ) :
    uniformProb (fun x : Fin k → A => ∀ i, x i ≠ a) =
      ((Fintype.card A - 1 : ℕ) / (Fintype.card A : ℝ)) ^ k := by
  rw [uniformProb_eq_card]
  have hc : Nat.card {x : Fin k → A // ∀ i, x i ≠ a} =
      (Fintype.card A - 1) ^ k := by
    calc
      _ = Fintype.card (Fin k → {b : A // b ≠ a}) :=
        (Nat.card_congr Equiv.subtypePiEquivPi).trans Nat.card_eq_fintype_card
      _ = _ := by simp [Fintype.card_subtype_compl]
  rw [hc, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow, div_pow]

private theorem uniformProb_le_missing {A : Type*} [Fintype A] {k : ℕ}
    (P : (Fin k → A) → Prop) (hP : ∀ x, P x → ∃ a, ∀ i, x i ≠ a) :
    uniformProb P ≤ ∑ a : A, uniformProb (fun x : Fin k → A => ∀ i, x i ≠ a) := by
  unfold uniformProb uniformMean
  rw [← Finset.sum_div, Finset.sum_comm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : P x
  · obtain ⟨a, ha⟩ := hP x hx
    calc
      indicator (P x) = indicator (∀ i, x i ≠ a) := by simp [indicator, hx, ha]
      _ ≤ ∑ b : A, indicator (∀ i, x i ≠ b) :=
        Finset.single_le_sum (fun b _ => indicator_nonneg (∀ i, x i ≠ b))
          (Finset.mem_univ a)
  · simp only [indicator, ite_eq_right hx]
    exact Finset.sum_nonneg fun a _ => indicator_nonneg (∀ i, x i ≠ a)

private theorem tupleGraph_pos {V : Type*} [Fintype V] {k : ℕ}
    (x : EdgeTuple V k) (i : Fin k) : 0 < tupleGraph x (x i).val := by
  unfold tupleGraph
  rw [Finset.card_pos]
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

private theorem colorable_missing {V : Type*} [Fintype V] {q k : ℕ}
    (hqn : q < Fintype.card V) (G : MGraph V) (x : EdgeTuple V k)
    (hc : Colorable q (G + tupleGraph x)) :
    ∃ e : Pair V, ∀ i, x i ≠ e := by
  obtain ⟨σ, hσ⟩ := hc
  obtain ⟨u, v, huv, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt σ (by simpa using hqn)
  have he : ∀ w : V, s(u, v) ≠ s(w, w) := by
    intro w hw
    rcases Sym2.eq_iff.mp hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact huv rfl
  refine ⟨⟨s(u, v), he⟩, ?_⟩
  intro i hi
  have hx : (x i).val = s(u, v) := congrArg Subtype.val hi
  have hpos : 0 < tupleGraph x s(u, v) := by
    simpa only [hx] using tupleGraph_pos x i
  exact hσ u v (lt_of_lt_of_le hpos (Nat.le_add_left _ _)) heq

private theorem summable_of_missing {A : Type*} [Fintype A] [Nonempty A]
    (P : ∀ k : ℕ, (Fin k → A) → Prop)
    (hP : ∀ k x, P k x → ∃ a, ∀ i, x i ≠ a) :
    Summable (fun k => uniformProb (P k)) := by
  let N := Fintype.card A
  have hN : 0 < N := Fintype.card_pos
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let r : ℝ := (N - 1 : ℕ) / (N : ℝ)
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hNreal.le
  have hr1 : r < 1 := by
    apply (div_lt_one hNreal).mpr
    exact_mod_cast Nat.sub_lt hN (by decide : 0 < 1)
  have hgeom : Summable (fun k : ℕ => (N : ℝ) * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (N : ℝ)
  apply hgeom.of_nonneg_of_le (fun k => uniformProb_nonneg (P k))
  intro k
  calc
    uniformProb (P k) ≤ ∑ a : A,
        uniformProb (fun x : Fin k → A => ∀ i, x i ≠ a) :=
      uniformProb_le_missing _ (hP k)
    _ = (N : ℝ) * r ^ k := by
      simp_rw [avoid_probability]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem survival_summable {V : Type*} [Fintype V] {q : ℕ}
    (hqn : q < Fintype.card V) (hpair : Nonempty (Pair V)) (G : MGraph V) :
    Summable (survival q G) := by
  let := hpair
  exact summable_of_missing (fun k x => Colorable q (G + tupleGraph x))
    (fun k x hx => colorable_missing hqn G x hx)

private theorem pair_nonempty {n : ℕ} (hn : 2 ≤ n) : Nonempty (Pair (Fin n)) := by
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro h
    have := congrArg Fin.val h
    norm_num [u, v] at this
  refine ⟨⟨s(u, v), ?_⟩⟩
  intro w hw
  rcases Sym2.eq_iff.mp hw with ⟨huw, hvw⟩ | ⟨huw, hvw⟩ <;>
    exact huv (huw.trans hvw.symm)

private theorem survival_zero_of_not_colorable {V : Type*} [Fintype V]
    {q : ℕ} {G : MGraph V} (hG : ¬ Colorable q G) (k : ℕ) : survival q G k = 0 := by
  have hx (x : EdgeTuple V k) : ¬ Colorable q (G + tupleGraph x) := by
    rintro ⟨σ, hσ⟩
    apply hG
    refine ⟨σ, ?_⟩
    intro u v huv
    exact hσ u v (lt_of_lt_of_le huv (Nat.le_add_right _ _))
  simp [survival, uniformProb, uniformMean, indicator, hx]

private theorem lifetimeReal_eq_tsum {V : Type*} [Fintype V] (q : ℕ) (G : MGraph V)
    (hs : Summable (survival q G)) : (∑' k : ℕ, survival q G k) = lifetimeReal q G := by
  have hn (k : ℕ) : 0 ≤ survival q G k := uniformProb_nonneg _
  unfold lifetimeReal lifetime
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs]
  exact (ENNReal.toReal_ofReal (tsum_nonneg hn)).symm

/-- Finite lifetimes and their real conversions, proved directly from finite pair sampling. -/
theorem S4_BRIDGE_03AStatement_holds : ThLean.BP.S4.S4_BRIDGE_03AStatement := by
  intro q n hq hn G _hG
  have hs : Summable (survival q G) :=
    survival_summable (by simpa using (show q < n by omega))
      (pair_nonempty (by omega)) G
  have hf : lifetime q G < ⊤ := hs.tsum_ofReal_lt_top
  have hsum := lifetimeReal_eq_tsum q G hs
  refine ⟨hf, hs, hsum, ?_, ?_, ?_⟩
  · intro y hy
    exact ENNReal.ofReal_lt_iff_lt_toReal hy (ne_of_lt hf)
  · intro a ha
    rw [ENNReal.toReal_min ENNReal.ofReal_ne_top (ne_of_lt hf)]
    simp [ENNReal.toReal_ofReal ha, lifetimeReal]
  · intro hnot
    have hz : lifetime q G = 0 := by
      simp [lifetime, survival_zero_of_not_colorable hnot]
    exact ⟨hz, by simp [lifetimeReal, hz]⟩

example : ThLean.BP.S4.S4_BRIDGE_03AStatement := S4_BRIDGE_03AStatement_holds

end ThLean.W.S436S

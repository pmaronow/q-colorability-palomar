module

public import ThLean.BP.SA.Quantiles

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ThLean.W.SA40S
open ThresholdFoundations

theorem ordered_pair_sum {V : Type*} [Fintype V] (f : Sym2 V → ℝ)
    (hdiag : ∀ v, f s(v, v) = 0) :
    (∑ xy : V × V, f s(xy.1, xy.2)) = 2 * ∑ e : Pair V, f e.val := by
  classical
  have hfiber (e : Sym2 V) :
      (∑ xy ∈ Finset.univ.filter (fun xy : V × V => s(xy.1, xy.2) = e), f e) =
        if ∀ v, e ≠ s(v, v) then 2 * f e else 0 := by
    induction e using Sym2.ind with
    | h a b =>
      have hset : Finset.univ.filter (fun xy : V × V => s(xy.1, xy.2) = s(a, b)) =
          {(a, b), (b, a)} := by
        ext xy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
        aesop
      rw [hset]
      by_cases hab : a = b
      · subst b
        simp [hdiag]
      · have hnon : ∀ v, s(a, b) ≠ s(v, v) := by
          intro v hv
          rcases Sym2.eq_iff.mp hv with h | h <;> exact hab (h.1.trans h.2.symm)
        simp [hab, hnon, two_mul]
  calc
    (∑ xy : V × V, f s(xy.1, xy.2)) =
        ∑ e : Sym2 V, ∑ xy ∈ Finset.univ.filter
          (fun xy : V × V => s(xy.1, xy.2) = e), f e :=
      (Finset.sum_fiberwise' Finset.univ (fun xy : V × V => s(xy.1, xy.2)) f).symm
    _ = ∑ e : Sym2 V, if ∀ v, e ≠ s(v, v) then 2 * f e else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      exact hfiber e
    _ = 2 * ∑ e : Pair V, f e.val := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

theorem sum_tuples_succ {A : Type*} [Fintype A] (m : ℕ)
    (f : (Fin (m + 1) → A) → ℝ) :
    (∑ x, f x) = ∑ a : A, ∑ x : Fin m → A, f (Fin.cons a x) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => A))]
  rw [Fintype.sum_prod_type]
  rfl

/-- Each nonloop has two orientations, independently at every tuple position. -/
theorem ordered_tuple_sum {V : Type*} [Fintype V] (m : ℕ)
    (f : (Fin m → Sym2 V) → ℝ)
    (hdiag : ∀ x i v, x i = s(v, v) → f x = 0) :
    (∑ x : Fin m → V × V, f ((fun xy : V × V => s(xy.1, xy.2)) ∘ x)) =
      (2 : ℝ) ^ m * ∑ y : Fin m → Pair V, f (Subtype.val ∘ y) := by
  classical
  induction m with
  | zero =>
    simp only [Fintype.sum_unique, pow_zero, one_mul]
    exact congrArg f (Subsingleton.elim _ _)
  | succ m ih =>
    have htail (xy : V × V) :
        (∑ x : Fin m → V × V,
          f (Fin.cons s(xy.1, xy.2) ((fun ab : V × V => s(ab.1, ab.2)) ∘ x))) =
        (2 : ℝ) ^ m * ∑ y : Fin m → Pair V,
          f (Fin.cons s(xy.1, xy.2) (Subtype.val ∘ y)) := by
      apply ih (fun z => f (Fin.cons s(xy.1, xy.2) z))
      intro x i v hv
      exact hdiag _ i.succ v (by simpa using hv)
    calc
      _ = ∑ xy : V × V, ∑ x : Fin m → V × V,
          f (Fin.cons s(xy.1, xy.2) ((fun ab : V × V => s(ab.1, ab.2)) ∘ x)) := by
        rw [sum_tuples_succ]
        simp only [Fin.comp_cons]
      _ = ∑ xy : V × V, (2 : ℝ) ^ m * ∑ y : Fin m → Pair V,
          f (Fin.cons s(xy.1, xy.2) (Subtype.val ∘ y)) := by
        exact Finset.sum_congr rfl (fun xy _ => htail xy)
      _ = (2 : ℝ) ^ m * ∑ y : Fin m → Pair V, ∑ xy : V × V,
          f (Fin.cons s(xy.1, xy.2) (Subtype.val ∘ y)) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ = (2 : ℝ) ^ m * ∑ y : Fin m → Pair V,
          2 * ∑ e : Pair V, f (Fin.cons e.val (Subtype.val ∘ y)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        exact ordered_pair_sum (fun e => f (Fin.cons e (Subtype.val ∘ y)))
          (fun v => hdiag (Fin.cons s(v, v) (Subtype.val ∘ y)) 0 v rfl)
      _ = (2 : ℝ) ^ (m + 1) * ∑ y : Fin (m + 1) → Pair V,
          f (Subtype.val ∘ y) := by
        rw [← Finset.mul_sum, sum_tuples_succ]
        simp only [Fin.comp_cons]
        rw [Finset.sum_comm, pow_succ]
        ring

theorem colorable_ordered_sum {V : Type*} [Fintype V] (q m : ℕ) :
    (∑ x : Fin m → V × V, indicator (Colorable q (orderedTupleGraph x))) =
      (2 : ℝ) ^ m * ∑ y : EdgeTuple V m, indicator (Colorable q (tupleGraph y)) := by
  classical
  let f : (Fin m → Sym2 V) → ℝ := fun x =>
    indicator (Colorable q (fun e => (Finset.univ.filter (fun i => x i = e)).card))
  apply ordered_tuple_sum m f
  intro x i v hv
  apply ite_eq_right
  intro ⟨σ, hσ⟩
  apply hσ v v ?_ rfl
  exact Finset.card_pos.mpr ⟨i, by simp [hv]⟩

theorem pair_card_fin (n : ℕ) [Fintype (Pair (Fin n))] :
    Fintype.card (Pair (Fin n)) = n.choose 2 := by
  let e : Pair (Fin n) ≃ {z : Sym2 (Fin n) // ¬ z.IsDiag} :=
    Equiv.subtypeEquivRight (fun z => by
      induction z using Sym2.ind with
      | h a b => simp [eq_comm])
  rw [Fintype.card_congr e, Sym2.card_subtype_not_diag, Fintype.card_fin]

/-- Conditioning every ordered sample to be a nonloop gives the ordinary process. -/
theorem ordered_colorable_probability (q n m : ℕ) (hn : 2 ≤ n) :
    uniformProb (fun x : Fin m → Fin n × Fin n => Colorable q (orderedTupleGraph x)) =
      (((n : ℝ) - 1) / n) ^ m * processSurvival (V := Fin n) q m := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp only [processSurvival, survival, zero_add, uniformProb, uniformMean]
  rw [colorable_ordered_sum]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_mul, pair_card_fin, Nat.cast_choose_two]
  simp only [mul_pow, div_pow]
  field_simp [hnpos.ne', hn1]

end ThLean.W.SA40S

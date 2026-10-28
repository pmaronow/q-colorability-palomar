import ThLean.BP.S3.Lifetime

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S330
open ThresholdFoundations

private theorem tupleGraph_append {V : Type*} [Fintype V] {m k : ℕ}
    (x : EdgeTuple V m) (y : EdgeTuple V k) :
    tupleGraph (Fin.append x y) = tupleGraph x + tupleGraph y := by
  classical
  funext e
  simp only [Pi.add_apply, tupleGraph, Finset.card_filter]
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp [finSumFinEquiv, Fin.append]

private theorem uniformMean_append {E : Type*} [Fintype E]
    (hE : Nonempty E) {m k : ℕ} (f : (Fin (m+k) → E) → ℝ) :
    uniformMean f = uniformMean (fun x : Fin m → E =>
      uniformMean (fun y : Fin k → E => f (Fin.append x y))) := by
  classical
  unfold uniformMean
  rw [← Equiv.sum_comp (Fin.appendEquiv m k) f, Fintype.sum_prod_type]
  have hc : Fintype.card (Fin (m+k) → E) =
      Fintype.card (Fin m → E) * Fintype.card (Fin k → E) := by
    rw [← Fintype.card_congr (Fin.appendEquiv m k), Fintype.card_prod]
  rw [hc]
  have hm : (Fintype.card (Fin m → E) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨fun _ => Classical.choice hE⟩))
  have hk : (Fintype.card (Fin k → E) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨fun _ => Classical.choice hE⟩))
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  push_cast
  field_simp [hm, hk]
  simp [Fin.appendEquiv]

private theorem uniformMean_const_mul_left {E : Type*} [Fintype E]
    (hE : Nonempty E) (c : ℝ) (f : E → ℝ) :
    uniformMean (fun x => c * f x) = c * uniformMean f := by
  classical
  unfold uniformMean
  rw [← Finset.mul_sum]
  have hc : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr hE))
  field_simp [hc]

private theorem pair_nonempty_of_card {V : Type*} [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  classical
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card V)
  refine ⟨⟨s(a,b), ?_⟩⟩
  intro v heq
  rcases (Sym2.eq_iff.mp heq) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hab (ha.trans hb.symm)
  · exact hab (ha.trans hb.symm)

private theorem survival_nonneg {V : Type*} [Fintype V] (q : ℕ)
    (G : MGraph V) (k : ℕ) : 0 ≤ survival q G k := by
  unfold survival uniformProb uniformMean indicator
  positivity

private theorem survival_summable_of_finite
    (h26 : ThLean.BP.S3.S3_26Statement.{u}) {V : Type u} [Fintype V] (q : ℕ)
    (hq : 2 ≤ q) (hV : 2*q ≤ Fintype.card V) (G : MGraph V) :
    Summable (fun k : ℕ => survival q G k) := by
  have hfinite : lifetime q G ≠ ⊤ := ((h26 V q hq hV).2.1 G).1
  have hsum : (∑' k : ℕ, ENNReal.ofReal (survival q G k)) ≠ ⊤ := by
    simpa [lifetime] using hfinite
  have hs := ENNReal.summable_toReal hsum
  convert hs using 1
  funext k
  exact (ENNReal.toReal_ofReal (survival_nonneg q G k)).symm

private theorem lifetimeReal_eq_tsum_survival
    {V : Type u} [Fintype V] (q : ℕ) (G : MGraph V) :
    lifetimeReal q G = ∑' k : ℕ, survival q G k := by
  rw [lifetimeReal, lifetime, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro k
  exact ENNReal.toReal_ofReal (survival_nonneg q G k)

/-- Deterministic-time averaging, using only the finite-lifetime bound. -/
theorem S3_28Statement_of_deps
    (h26 : ThLean.BP.S3.S3_26Statement.{u}) : ThLean.BP.S3.S3_28Statement.{u} := by
  intro V _ q hq hV m z hz
  have hPair : Nonempty (Pair V) := pair_nonempty_of_card (by omega)
  let a : ℕ → ℝ := fun k => uniformMean (fun x : EdgeTuple V (m+k) =>
    z (fun i => x (Fin.castAdd k i)) * indicator (Colorable q (tupleGraph x)))
  have ha (k : ℕ) : a k = uniformMean (fun x : EdgeTuple V m =>
      z x * survival q (tupleGraph x) k) := by
    dsimp [a]
    rw [uniformMean_append hPair]
    simp only [Fin.append_left, tupleGraph_append]
    simp only [survival, uniformProb]
    congr 1
    funext x
    exact uniformMean_const_mul_left (by exact ⟨fun _ => Classical.choice hPair⟩) (z x) (fun y : EdgeTuple V k =>
      indicator (Colorable q (tupleGraph x + tupleGraph y)))
  have hterm (x : EdgeTuple V m) :
      Summable (fun k : ℕ => z x * survival q (tupleGraph x) k) :=
    (survival_summable_of_finite h26 q hq hV (tupleGraph x)).mul_left (z x)
  have hfiniteSum : Summable (fun k : ℕ =>
      ∑ x : EdgeTuple V m, z x * survival q (tupleGraph x) k) := by
    apply summable_sum
    intro x hx
    exact hterm x
  have haSummable : Summable a := by
    have h := hfiniteSum.div_const (Fintype.card (EdgeTuple V m) : ℝ)
    have haEq : a = fun k : ℕ =>
        (∑ x : EdgeTuple V m, z x * survival q (tupleGraph x) k) /
          (Fintype.card (EdgeTuple V m) : ℝ) := by
      funext k
      rw [ha k]
      rfl
    rw [haEq]
    exact h
  have hsumSwap : (∑' k : ℕ,
      ∑ x : EdgeTuple V m, z x * survival q (tupleGraph x) k) =
      ∑ x : EdgeTuple V m, ∑' k : ℕ, z x * survival q (tupleGraph x) k := by
    exact Summable.tsum_finsetSum (fun x hx => hterm x)
  have hsumEq : (∑' k : ℕ, a k) =
      uniformMean (fun x : EdgeTuple V m => z x * lifetimeReal q (tupleGraph x)) := by
    calc
      (∑' k : ℕ, a k) =
          ∑' k : ℕ, (∑ x : EdgeTuple V m,
            z x * survival q (tupleGraph x) k) /
              (Fintype.card (EdgeTuple V m) : ℝ) := by
        apply tsum_congr
        intro k
        rw [ha k]
        rfl
      _ = (∑ x : EdgeTuple V m,
          ∑' k : ℕ, z x * survival q (tupleGraph x) k) /
            (Fintype.card (EdgeTuple V m) : ℝ) := by
        rw [tsum_div_const, hsumSwap]
      _ = uniformMean (fun x : EdgeTuple V m =>
          z x * lifetimeReal q (tupleGraph x)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        rw [tsum_mul_left, ← lifetimeReal_eq_tsum_survival q (tupleGraph x)]
  exact ⟨haSummable, hsumEq⟩

end ThLean.W.S330

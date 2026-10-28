import ThLean.BP.S3.Poisson

noncomputable section
open scoped BigOperators
universe u
attribute [local instance] Classical.propDecidable
namespace ThLean.W.S336
open ThresholdFoundations ThLean.BP.S3

theorem weightedListMean_eq_tsum (h32 : S3_32Statement.{u})
    {E : Type u} [Fintype E] [Nonempty E] (ν : E → ℝ) (z : ℝ)
    (hν : IsProbabilityVector ν) (hz : 0 ≤ z) (f : List E → ℝ)
    (hf0 : ∀ xs, 0 ≤ f xs) (hf1 : ∀ xs, f xs ≤ 1) :
    weightedListMean z ν f = ∑' xs : List E, poissonListMass z ν xs * f xs := by
  have hmass := (h32 E ν z hν hz).1
  have hmass0 (xs : List E) : 0 ≤ poissonListMass z ν xs := by
    unfold poissonListMass poissonWeight
    apply mul_nonneg
    · exact div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg hz _)) (Nat.cast_nonneg _)
    · exact List.prod_nonneg (s := xs.map ν) (by
        intro x hx
        rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
        exact hν.1 e)
  have hweighted : Summable (fun xs : List E => poissonListMass z ν xs * f xs) :=
    hmass.of_nonneg_of_le
      (fun xs => mul_nonneg (hmass0 xs) (hf0 xs))
      (fun xs => by
        have := mul_nonneg (hmass0 xs) (sub_nonneg.mpr (hf1 xs))
        nlinarith)
  have hSigma : Summable (fun p : Σ k : ℕ, Fin k → E =>
      poissonListMass z ν (List.ofFn p.2) * f (List.ofFn p.2)) := by
    change Summable ((fun xs : List E => poissonListMass z ν xs * f xs) ∘
      List.equivSigmaTuple.symm)
    exact (List.equivSigmaTuple.symm).summable_iff.mpr hweighted
  calc
    weightedListMean z ν f =
        ∑' k : ℕ, ∑' x : Fin k → E,
          poissonListMass z ν (List.ofFn x) * f (List.ofFn x) := by
      unfold weightedListMean poissonMixture
      apply tsum_congr
      intro k
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(h32 E ν z hν hz).2.2.2 k x]
      simp [poissonListMass, List.prod_ofFn, mul_assoc]
    _ = ∑' p : Σ k : ℕ, Fin k → E,
          poissonListMass z ν (List.ofFn p.2) * f (List.ofFn p.2) := by
      exact (hSigma.tsum_sigma' (fun k => Summable.of_finite)).symm
    _ = ∑' xs : List E, poissonListMass z ν xs * f xs := by
      exact (List.equivSigmaTuple.symm).tsum_eq
        (fun xs : List E => poissonListMass z ν xs * f xs)

theorem weightedListMean_split_event (h32 : S3_32Statement.{u})
    (h34 : S3_34Statement.{u}) {E : Type u} [Fintype E] [Nonempty E]
    (ν : E → ℝ) (b : E → Bool) (z p r : ℝ)
    (hν : IsProbabilityVector ν) (hz : 0 ≤ z) (hp : 0 < p) (hr : 0 < r)
    (hpdef : (∑ e : E, if b e then ν e else 0) = p)
    (hrdef : (∑ e : E, if b e then 0 else ν e) = r)
    (u : List E) (hu : ∀ e ∈ u, b e = true)
    (Q : List E → Prop) (hQ : ∀ v, Q v → ∀ e ∈ v, b e = false) :
    weightedListMean z ν (fun w => indicator
      (w.filter b = u ∧ Q (w.filter (fun e => !b e)))) =
      poissonListMass (z*p) (fun e => ν e/p) u *
        weightedListMean (z*r) (fun e => if b e then 0 else ν e/r)
          (fun v => indicator (Q v)) := by
  let yes : E → Bool := b
  let getNo : List E → List E := fun w => w.filter (fun e => !b e)
  have hmass0 (w : List E) : 0 ≤ poissonListMass z ν w := by
    unfold poissonListMass poissonWeight
    apply mul_nonneg
    · exact div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg hz _)) (Nat.cast_nonneg _)
    · exact List.prod_nonneg (s := w.map ν) (by
        intro x hx
        rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
        exact hν.1 e)
  have hf0 (w : List E) : 0 ≤ indicator (w.filter yes = u ∧ Q (getNo w)) := by
    unfold indicator
    split_ifs <;> norm_num
  have hf1 (w : List E) : indicator (w.filter yes = u ∧ Q (getNo w)) ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  have hsum : Summable (fun w : List E => poissonListMass z ν w *
      indicator (w.filter yes = u ∧ Q (getNo w))) := by
    have hm := (h32 E ν z hν hz).1
    exact hm.of_nonneg_of_le
      (fun w => mul_nonneg (hmass0 w) (hf0 w))
      (fun w => by nlinarith [mul_nonneg (hmass0 w) (sub_nonneg.mpr (hf1 w))])
  have hfib (v : List E) : Summable (fun w : {w : List E // getNo w = v} =>
      poissonListMass z ν w.1 * indicator (w.1.filter yes = u ∧ Q v)) := by
    have hsub := (h32 E ν z hν hz).1.subtype (fun w : List E => getNo w = v)
    have hi0 (w : {w : List E // getNo w = v}) :
        0 ≤ indicator (w.1.filter yes = u ∧ Q v) := by
      unfold indicator
      split_ifs <;> norm_num
    exact hsub.of_nonneg_of_le
      (fun w => mul_nonneg (hmass0 w.1) (hi0 w))
      (fun w => by
        have hI : indicator (w.1.filter yes = u ∧ Q v) ≤ 1 := by
          unfold indicator
          split_ifs <;> norm_num
        have hI0 := hi0 w
        calc
          poissonListMass z ν w.1 * indicator (w.1.filter yes = u ∧ Q v) ≤
              poissonListMass z ν w.1 * 1 :=
            mul_le_mul_of_nonneg_left hI (hmass0 w.1)
          _ = poissonListMass z ν w.1 := mul_one _)
  have hSigma : Summable (fun s : Σ v : List E, {w : List E // getNo w = v} =>
      poissonListMass z ν s.2.1 * indicator (s.2.1.filter yes = u ∧ Q s.1)) := by
    let e := Equiv.sigmaFiberEquiv getNo
    have ht : Summable ((fun w : List E => poissonListMass z ν w *
        indicator (w.filter yes = u ∧ Q (getNo w))) ∘ e) := e.summable_iff.mpr hsum
    exact ht.congr (fun s => by
      change poissonListMass z ν s.2.1 * indicator
          (s.2.1.filter yes = u ∧ Q (getNo s.2.1)) =
        poissonListMass z ν s.2.1 * indicator (s.2.1.filter yes = u ∧ Q s.1)
      rw [s.2.2])
  calc
    weightedListMean z ν (fun w => indicator (w.filter yes = u ∧ Q (getNo w))) =
        ∑' w : List E, poissonListMass z ν w * indicator
          (w.filter yes = u ∧ Q (getNo w)) :=
      weightedListMean_eq_tsum h32 ν z hν hz _ hf0 hf1
    _ = ∑' s : Σ v : List E, {w : List E // getNo w = v},
          poissonListMass z ν s.2.1 * indicator (s.2.1.filter yes = u ∧ Q s.1) := by
      let e := Equiv.sigmaFiberEquiv getNo
      symm
      calc
        _ = ∑' s : Σ v : List E, {w : List E // getNo w = v},
              poissonListMass z ν s.2.1 * indicator
                (s.2.1.filter yes = u ∧ Q (getNo s.2.1)) := by
          apply tsum_congr
          intro s
          rw [s.2.2]
        _ = ∑' w : List E, poissonListMass z ν w *
              indicator (w.filter yes = u ∧ Q (getNo w)) := by
          simpa [e, Equiv.sigmaFiberEquiv] using
            e.tsum_eq (fun w : List E => poissonListMass z ν w *
              indicator (w.filter yes = u ∧ Q (getNo w)))
    _ = ∑' v : List E, ∑' w : {w : List E // getNo w = v},
          poissonListMass z ν w.1 * indicator (w.1.filter yes = u ∧ Q v) := by
      exact hSigma.tsum_sigma' hfib
    _ = ∑' v : List E, if Q v then
          poissonListMass (z*p) (fun e => ν e/p) u *
            poissonListMass (z*r) (fun e => ν e/r) v else 0 := by
      congr 1
      funext v
      by_cases hq : Q v
      · simp only [hq, if_pos]
        have hv := hQ v hq
        have hfiber : (∑' w : {w : List E // getNo w = v},
            poissonListMass z ν w.1 * indicator (w.1.filter yes = u)) =
            ∑' w : List E, if w.filter yes = u ∧
              w.filter (fun e => !yes e) = v then poissonListMass z ν w else 0 := by
          change (∑' w : ↑{w : List E | getNo w = v},
            poissonListMass z ν w.1 * indicator (w.1.filter yes = u)) = _
          rw [tsum_subtype {w : List E | getNo w = v}
            (fun w => poissonListMass z ν w * indicator (w.filter yes = u))]
          apply tsum_congr
          intro w
          by_cases hw : getNo w = v
          · have hw' : w.filter (fun e => !yes e) = v := by
              simpa [getNo, yes] using hw
            simp [Set.indicator, indicator, hw, hw']
          · have hw' : w.filter (fun e => !yes e) ≠ v := by
              intro h
              apply hw
              simpa [getNo, yes] using h
            simp [Set.indicator, indicator, hw, hw']
        simp only [hq, and_true]
        rw [hfiber]
        have h34' := h34 E ν yes z hν hz
          (by rw [hpdef]; exact hp) (by rw [hrdef]; exact hr) u v hu hv
        simpa [hpdef, hrdef, indicator, mul_assoc, yes] using h34'
      · simp [hq, indicator]
    _ = poissonListMass (z*p) (fun e => ν e/p) u *
          weightedListMean (z*r) (fun e => if b e then 0 else ν e/r)
            (fun v => indicator (Q v)) := by
      let ν' : E → ℝ := fun e => if b e then 0 else ν e/r
      have hν' : IsProbabilityVector ν' := by
        constructor
        · intro e
          by_cases hb : b e = true
          · simp [ν', hb]
          · simp [ν', hb, div_nonneg (hν.1 e) hr.le]
        · dsimp [ν']
          calc
            (∑ e : E, if b e then 0 else ν e/r) =
                (∑ e : E, if b e then 0 else ν e)/r := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro e he
              by_cases hb : b e = true <;> simp [hb]
            _ = r/r := by rw [hrdef]
            _ = 1 := div_self hr.ne'
      have hzr : 0 ≤ z*r := mul_nonneg hz hr.le
      have hf0' (v : List E) : 0 ≤ indicator (Q v) := by
        unfold indicator
        split_ifs <;> norm_num
      have hf1' (v : List E) : indicator (Q v) ≤ 1 := by
        unfold indicator
        split_ifs <;> norm_num
      rw [weightedListMean_eq_tsum h32 ν' (z*r) hν' hzr
        (fun v => indicator (Q v)) hf0' hf1']
      rw [← tsum_mul_left]
      apply tsum_congr
      intro v
      by_cases hq : Q v
      · have hv := hQ v hq
        have hmap : v.map (fun e => ν e/r) = v.map ν' := by
          apply List.map_congr_left
          intro e he
          simp [ν', hv e he]
        have hmassv : poissonListMass (z*r) (fun e => ν e/r) v =
            poissonListMass (z*r) ν' v := by
          unfold poissonListMass
          rw [hmap]
        rw [hmassv]
        simp [hq, indicator]
      · simp [hq, indicator]

end ThLean.W.S336

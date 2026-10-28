import ThLean.BP.S3.Poisson

noncomputable section
open scoped BigOperators
open ThresholdFoundations
namespace ThLean.W.S335
universe u

private theorem list_prod_div_const {E : Type*} (xs : List E) (f : E → ℝ)
    (p : ℝ) (hp : p ≠ 0) :
    (xs.map (fun e => f e / p)).prod = (xs.map f).prod / p ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [ih, pow_succ]
      field_simp [hp]

private theorem poisson_split_scalar (z p r : ℝ) (a b : ℕ) (U V : ℝ)
    (hpr : p + r = 1) (hp : p ≠ 0) (hr : r ≠ 0) :
    (Nat.choose (a + b) a : ℝ) *
        (poissonWeight z (a + b) * (U * V)) =
      (poissonWeight (z * p) a * (U / p ^ a)) *
        (poissonWeight (z * r) b * (V / r ^ b)) := by
  have hfacN : Nat.choose (a + b) a * a.factorial * b.factorial = (a + b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    simpa [Nat.add_sub_cancel_left] using h
  have hfac : (Nat.choose (a + b) a : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ) =
      ((a + b).factorial : ℝ) := by
    exact_mod_cast hfacN
  have hfa : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hfb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  have hfn : ((a + b).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (a + b)
  have hcoef : (Nat.choose (a + b) a : ℝ) / ((a + b).factorial : ℝ) =
      1 / ((a.factorial : ℝ) * (b.factorial : ℝ)) := by
    field_simp [hfa, hfb, hfn]
    nlinarith [hfac]
  have hpow : z * p + z * r = z := by
    calc
      z * p + z * r = z * (p + r) := by ring
      _ = z := by simp [hpr]
  have hexp : Real.exp (-(z * p)) * Real.exp (-(z * r)) = Real.exp (-z) := by
    rw [← Real.exp_add]
    congr 1
    nlinarith [hpow]
  simp only [poissonWeight]
  calc
    (Nat.choose (a + b) a : ℝ) *
        (Real.exp (-z) * z ^ (a + b) / ((a + b).factorial : ℝ) * (U * V)) =
      Real.exp (-z) * z ^ a * z ^ b * (U * V) *
        ((Nat.choose (a + b) a : ℝ) / ((a + b).factorial : ℝ)) := by
          rw [pow_add]
          ring
    _ = Real.exp (-z) * z ^ a * z ^ b * (U * V) *
        (1 / ((a.factorial : ℝ) * (b.factorial : ℝ))) := by rw [hcoef]
    _ = Real.exp (-(z * p)) * Real.exp (-(z * r)) * z ^ a * z ^ b *
        (U * V) * (1 / ((a.factorial : ℝ) * (b.factorial : ℝ))) := by
          rw [← hexp]
    _ = (Real.exp (-(z * p)) * (z * p) ^ a / (a.factorial : ℝ) *
          (U / p ^ a)) *
        (Real.exp (-(z * r)) * (z * r) ^ b / (b.factorial : ℝ) *
          (V / r ^ b)) := by
          rw [mul_pow, mul_pow]
          field_simp [hp, hr, hfa, hfb]

/-- Binary Poisson-word splitting from the finite shuffle count. -/
theorem S3_34Statement_of_deps (h33 : ThLean.BP.S3.S3_33Statement.{u}) :
    ThLean.BP.S3.S3_34Statement.{u} := by
  intro E instF instNE ν label z hν hz p r hp hr u v hu hv
  classical
  let A : Set (List E) :=
    {w | w.filter label = u ∧ w.filter (fun e => !(label e)) = v}
  rcases h33 E label u v hu hv with ⟨hfinite, hcard, hword⟩
  have hpr : p + r = 1 := by
    have he : ∀ e : E,
        (if label e then ν e else 0) + (if label e then 0 else ν e) = ν e := by
      intro e
      cases label e <;> simp
    dsimp [p, r]
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun e _ => he e)]
    exact hν.2
  let C : ℝ := poissonWeight z (u.length + v.length) *
    ((u.map ν).prod * (v.map ν).prod)
  have hterm : ∀ w ∈ hfinite.toFinset,
      (if w.filter label = u ∧ w.filter (fun e => !(label e)) = v
        then poissonListMass z ν w else 0) = C := by
    intro w hw
    have hwA : w ∈ A := by simpa [A, Set.mem_ofPred_eq] using hw
    rcases hword w hwA with ⟨hlen, hprod⟩
    have hw1 : w.filter label = u := hwA.1
    have hw2 : w.filter (fun e => !(label e)) = v := hwA.2
    simp [C, hw1, hw2, hlen, hprod ν, poissonListMass]
  have hzero : ∀ w ∉ hfinite.toFinset,
      (if w.filter label = u ∧ w.filter (fun e => !(label e)) = v
        then poissonListMass z ν w else 0) = 0 := by
    intro w hw
    have hwA : w ∉ A := by simpa [A, Set.mem_ofPred_eq] using hw
    have hcond : ¬(w.filter label = u ∧ w.filter (fun e => !(label e)) = v) := by
      simpa [A] using hwA
    simp [hcond]
  calc
    (∑' w : List E,
        if w.filter label = u ∧ w.filter (fun e => !(label e)) = v
          then poissonListMass z ν w else 0) =
      ∑ w ∈ hfinite.toFinset,
        (if w.filter label = u ∧ w.filter (fun e => !(label e)) = v
          then poissonListMass z ν w else 0) := by
            exact tsum_eq_sum hzero
    _ = ∑ w ∈ hfinite.toFinset, C := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hterm w hw
    _ = (hfinite.toFinset.card : ℝ) * C := by simp
    _ = (A.ncard : ℝ) * C := by rw [Set.ncard_eq_toFinset_card A hfinite]
    _ = (Nat.choose (u.length + v.length) u.length : ℝ) * C := by
      rw [hcard]
    _ = (poissonListMass (z * p) (fun e => ν e / p) u) *
        (poissonListMass (z * r) (fun e => ν e / r) v) := by
      dsimp [C]
      rw [poissonListMass, poissonListMass,
        list_prod_div_const u ν p (ne_of_gt hp),
        list_prod_div_const v ν r (ne_of_gt hr)]
      exact poisson_split_scalar z p r u.length v.length
        (u.map ν).prod (v.map ν).prod hpr (ne_of_gt hp) (ne_of_gt hr)

end ThLean.W.S335

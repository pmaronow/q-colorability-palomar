import ThLean.BP.SA.Analytic

noncomputable section
open scoped BigOperators
namespace ThLean.W.SA30
open ThLean.BP.SA ThresholdFoundations

private lemma iteratedDeriv_poissonWeight_bound (R : ℝ) (hR : 0 ≤ R)
    (m k : ℕ) (x : ℝ) (hx : |x| ≤ R) :
    ‖iteratedFDeriv ℝ m (fun y : ℝ => poissonWeight y k) x‖ ≤
      Real.exp R * (2 : ℝ)^m * ((k + 1 : ℕ) : ℝ)^m *
        (R + 1)^k / (Nat.factorial k : ℝ) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hmul := iteratedDeriv_mul
    (f := fun y : ℝ => Real.exp (-y))
    (g := fun y : ℝ => y ^ k / (Nat.factorial k : ℝ))
    (n := m) (x := x) (by fun_prop) (by fun_prop)
  have hmul' : iteratedDeriv m
      (fun y : ℝ => Real.exp (-y) * (y ^ k / (Nat.factorial k : ℝ))) x =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        iteratedDeriv i (fun y : ℝ => Real.exp (-y)) x *
        iteratedDeriv (m - i) (fun y : ℝ => y ^ k / (Nat.factorial k : ℝ)) x := by
    convert hmul using 1
  have heq : (fun y : ℝ => poissonWeight y k) =
      (fun y : ℝ => Real.exp (-y) * (y ^ k / (Nat.factorial k : ℝ))) := by
    funext y
    simp [poissonWeight, div_eq_mul_inv, mul_assoc]
  rw [heq, hmul']
  calc
    ‖∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        iteratedDeriv i (fun y : ℝ => Real.exp (-y)) x *
        iteratedDeriv (m - i) (fun y : ℝ => y ^ k / (Nat.factorial k : ℝ)) x‖
      ≤ ∑ i ∈ Finset.range (m + 1), ‖(m.choose i : ℝ) *
        iteratedDeriv i (fun y : ℝ => Real.exp (-y)) x *
        iteratedDeriv (m - i) (fun y : ℝ => y ^ k / (Nat.factorial k : ℝ)) x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (Real.exp R * ((k + 1 : ℕ) : ℝ)^m * (R + 1)^k / (Nat.factorial k : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ m := by simp only [Finset.mem_range] at hi; omega
      have hs : m - i ≤ m := Nat.sub_le _ _
      have hexpEq : iteratedDeriv i (fun y : ℝ => Real.exp (-y)) x =
          (-1 : ℝ)^i * Real.exp (-x) := by
        simpa only [neg_one_mul] using
          (congrFun (iteratedDeriv_exp_const_mul i (-1)) x)
      have hexp : ‖iteratedDeriv i (fun y : ℝ => Real.exp (-y)) x‖ ≤ Real.exp R := by
        rw [hexpEq]
        have hxexp : -x ≤ R := by nlinarith [abs_le.mp hx]
        calc
          ‖(-1 : ℝ)^i * Real.exp (-x)‖ = Real.exp (-x) := by
            simp [Real.norm_eq_abs]
          _ ≤ Real.exp R := Real.exp_le_exp.mpr hxexp
      have hpow : iteratedDeriv (m - i)
          (fun y : ℝ => y ^ k / (Nat.factorial k : ℝ)) x =
          (k.descFactorial (m - i) : ℝ) * x ^ (k - (m - i)) /
            (Nat.factorial k : ℝ) := by
        simp [iteratedDeriv_div_const, iteratedDeriv_pow]
      rw [hpow]
      have hdf : (k.descFactorial (m - i) : ℝ) ≤ ((k + 1 : ℕ) : ℝ)^m := by
        have hnat : k.descFactorial (m - i) ≤ (k + 1)^(m - i) := by
          exact (Nat.descFactorial_le_pow k (m - i)).trans (by
            gcongr
            exact Nat.le_succ k)
        exact_mod_cast (hnat.trans (by gcongr))
      have hxpow : ‖x‖^(k - (m - i)) ≤ (R + 1)^k := by
        have hbase : ‖x‖ ≤ R + 1 := by
          rw [Real.norm_eq_abs]
          exact le_trans hx (by linarith)
        calc
          ‖x‖^(k - (m - i)) ≤ (R + 1)^(k - (m - i)) := by gcongr
          _ ≤ (R + 1)^k := pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
      have hchoose : 0 ≤ (m.choose i : ℝ) := by positivity
      have hfact : 0 < (Nat.factorial k : ℝ) := by positivity
      have hexp0 : 0 ≤ Real.exp R := Real.exp_pos R |>.le
      have hdf0 : 0 ≤ (k.descFactorial (m - i) : ℝ) := by positivity
      have hxpow0 : 0 ≤ ‖x‖^(k - (m - i)) := by positivity
      have hpoly : ‖x ^ (k - (m - i))‖ ≤ (R + 1)^k := by
        simpa only [norm_pow] using hxpow
      simp only [norm_mul, norm_div, Real.norm_eq_abs, abs_of_nonneg hchoose,
        abs_of_nonneg hdf0, abs_of_pos hfact]
      have hterm := mul_le_mul hdf hpoly (by positivity) (by positivity)
      have hterm' : (k.descFactorial (m - i) : ℝ) *
          ‖x ^ (k - (m - i))‖ ≤ ((k + 1 : ℕ) : ℝ)^m * (R + 1)^k := hterm
      have hdiv : (k.descFactorial (m - i) : ℝ) *
          ‖x ^ (k - (m - i))‖ / (Nat.factorial k : ℝ) ≤
          (((k + 1 : ℕ) : ℝ)^m * (R + 1)^k) / (Nat.factorial k : ℝ) :=
        div_le_div_of_nonneg_right hterm' (le_of_lt hfact)
      have hfirst : (m.choose i : ℝ) *
          ‖iteratedDeriv i (fun y : ℝ => Real.exp (-y)) x‖ ≤
          (m.choose i : ℝ) * Real.exp R := mul_le_mul_of_nonneg_left hexp hchoose
      calc
        (m.choose i : ℝ) * (‖iteratedDeriv i (fun y : ℝ => Real.exp (-y)) x‖) *
            ((k.descFactorial (m - i) : ℝ) * ‖x ^ (k - (m - i))‖ /
              (Nat.factorial k : ℝ))
          ≤ (m.choose i : ℝ) * Real.exp R *
              ((k.descFactorial (m - i) : ℝ) * ‖x ^ (k - (m - i))‖ /
                (Nat.factorial k : ℝ)) :=
              mul_le_mul_of_nonneg_right hfirst (by positivity)
        _ ≤ (m.choose i : ℝ) * Real.exp R *
              (((k + 1 : ℕ) : ℝ)^m * (R + 1)^k / (Nat.factorial k : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = (m.choose i : ℝ) *
              (Real.exp R * ((k + 1 : ℕ) : ℝ)^m * (R + 1)^k /
                (Nat.factorial k : ℝ)) := by ring
    _ = Real.exp R * (2 : ℝ)^m * ((k + 1 : ℕ) : ℝ)^m *
          (R + 1)^k / (Nat.factorial k : ℝ) := by
      rw [← Finset.sum_mul]
      have hchoose : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = (2 : ℝ)^m := by
        exact_mod_cast Nat.sum_range_choose m
      rw [hchoose]
      ring

private lemma uniformMean_bounds {A : Type} [Fintype A] (f : A → ℝ)
    (hlo : ∀ a, 0 ≤ f a) (hhi : ∀ a, f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 := by
  classical
  by_cases hne : Nonempty A
  · letI := hne
    unfold uniformMean
    have hcard : 0 < (Fintype.card A : ℝ) := by positivity
    constructor
    · exact div_nonneg (Finset.sum_nonneg fun a ha => hlo a) hcard.le
    · apply (div_le_one hcard).2
      calc
        (∑ a : A, f a) ≤ ∑ a : A, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          exact hhi a
        _ = (Fintype.card A : ℝ) := by simp
  · have hempty : IsEmpty A := not_nonempty_iff.mp hne
    letI := hempty
    simp [uniformMean]

private lemma interpolationCoefficient_bounds (q n₁ n₂ : ℕ)
    (k : Fin 3 → ℕ) :
    0 ≤ interpolationCoefficient q n₁ n₂ k ∧
      interpolationCoefficient q n₁ n₂ k ≤ 1 := by
  classical
  unfold interpolationCoefficient
  have hinner : ∀ (x₀ : Fin (k 0) → Fin (n₁ + n₂) × Fin (n₁ + n₂))
      (x₁ : Fin (k 1) → Fin n₁ × Fin n₁),
      0 ≤ uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
        indicator (Colorable q (mixedGraph x₀ x₁ x₂))) ∧
      uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
        indicator (Colorable q (mixedGraph x₀ x₁ x₂))) ≤ 1 := by
    intro x₀ x₁
    apply uniformMean_bounds
    · intro x₂
      by_cases hcolor : Colorable q (mixedGraph x₀ x₁ x₂) <;>
        simp [indicator, hcolor]
    · intro x₂
      by_cases hcolor : Colorable q (mixedGraph x₀ x₁ x₂) <;>
        simp [indicator, hcolor]
  have hmid : ∀ x₀ : Fin (k 0) → Fin (n₁ + n₂) × Fin (n₁ + n₂),
      0 ≤ uniformMean (fun x₁ : Fin (k 1) → Fin n₁ × Fin n₁ =>
        uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂)))) ∧
      uniformMean (fun x₁ : Fin (k 1) → Fin n₁ × Fin n₁ =>
        uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂)))) ≤ 1 := by
    intro x₀
    apply uniformMean_bounds
    · intro x₁
      exact (hinner x₀ x₁).1
    · intro x₁
      exact (hinner x₀ x₁).2
  exact uniformMean_bounds
    (fun x₀ : Fin (k 0) → Fin (n₁ + n₂) × Fin (n₁ + n₂) =>
      uniformMean (fun x₁ : Fin (k 1) → Fin n₁ × Fin n₁ =>
        uniformMean (fun x₂ : Fin (k 2) → Fin n₂ × Fin n₂ =>
          indicator (Colorable q (mixedGraph x₀ x₁ x₂)))))
    (fun x₀ => (hmid x₀).1) (fun x₀ => (hmid x₀).2)

private def poissonCubeFactor (R : ℝ) (r k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ)^r * (R + 1)^k / (Nat.factorial k : ℝ)

private def poissonCubeScale (R : ℝ) (r : ℕ) : ℝ :=
  Real.exp R * (2 : ℝ)^r

private def interpolationCubeConstant (R : ℝ) (r : ℕ) : ℝ :=
  1 + ∑ p ∈ (Finset.univ : Finset (Fin 3)).sym r,
    ((p : Multiset (Fin 3)).countPerms : ℝ) * (poissonCubeScale R r)^3

private lemma interpolationCubeConstant_pos (R : ℝ) (r : ℕ) :
    0 < interpolationCubeConstant R r := by
  unfold interpolationCubeConstant
  have hs : 0 ≤ ∑ p ∈ (Finset.univ : Finset (Fin 3)).sym r,
      ((p : Multiset (Fin 3)).countPerms : ℝ) * (poissonCubeScale R r)^3 := by
    apply Finset.sum_nonneg
    intro p hp
    have hcount : 0 ≤ ((p : Multiset (Fin 3)).countPerms : ℝ) := Nat.cast_nonneg _
    have hscale : 0 ≤ poissonCubeScale R r := by
      unfold poissonCubeScale
      positivity
    exact mul_nonneg hcount (pow_nonneg hscale 3)
  linarith

private lemma norm_proj_fin3 (i : Fin 3) :
    ‖(ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa [ContinuousLinearMap.proj_apply] using (norm_le_pi_norm x i)

private lemma coordinatePoissonWeight_bound (R : ℝ) (hR : 0 ≤ R) (r s : ℕ)
    (hs : s ≤ r) (k : Fin 3 → ℕ) (i : Fin 3) (μ : Fin 3 → ℝ)
    (hμ : ∀ j, |μ j| ≤ R) :
    ‖iteratedFDeriv ℝ s (fun z : Fin 3 → ℝ => poissonWeight (z i) (k i)) μ‖ ≤
      poissonCubeScale R r * poissonCubeFactor R r (k i) := by
  let P : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hP : ‖P‖ ≤ 1 := norm_proj_fin3 i
  have houter : ‖iteratedFDeriv ℝ s (fun x : ℝ => poissonWeight x (k i)) (μ i)‖ ≤
      poissonCubeScale R r * poissonCubeFactor R r (k i) := by
    have hsmall := iteratedDeriv_poissonWeight_bound R hR s (k i) (μ i) (hμ i)
    calc
      ‖iteratedFDeriv ℝ s (fun x : ℝ => poissonWeight x (k i)) (μ i)‖ ≤
          Real.exp R * (2 : ℝ)^s * ((k i + 1 : ℕ) : ℝ)^s *
            (R + 1)^(k i) / (Nat.factorial (k i) : ℝ) := hsmall
      _ ≤ poissonCubeScale R r * poissonCubeFactor R r (k i) := by
        unfold poissonCubeScale poissonCubeFactor
        have h2 : (2 : ℝ)^s ≤ (2 : ℝ)^r :=
          pow_le_pow_right₀ (by norm_num) hs
        have hk : ((k i + 1 : ℕ) : ℝ)^s ≤ ((k i + 1 : ℕ) : ℝ)^r := by
          apply pow_le_pow_right₀
          · exact_mod_cast (show 1 ≤ k i + 1 by omega)
          · exact hs
        have hpow : (2 : ℝ)^s * ((k i + 1 : ℕ) : ℝ)^s ≤
            (2 : ℝ)^r * ((k i + 1 : ℕ) : ℝ)^r :=
          mul_le_mul h2 hk (by positivity) (by positivity)
        have hmain : Real.exp R * ((2 : ℝ)^s * ((k i + 1 : ℕ) : ℝ)^s) ≤
            Real.exp R * ((2 : ℝ)^r * ((k i + 1 : ℕ) : ℝ)^r) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos R).le
        have htail : 0 ≤ (R + 1)^(k i) / (Nat.factorial (k i) : ℝ) := by positivity
        calc
          Real.exp R * (2 : ℝ)^s * ((k i + 1 : ℕ) : ℝ)^s *
              (R + 1)^(k i) / (Nat.factorial (k i) : ℝ)
            = (Real.exp R * ((2 : ℝ)^s * ((k i + 1 : ℕ) : ℝ)^s)) *
                ((R + 1)^(k i) / (Nat.factorial (k i) : ℝ)) := by ring
          _ ≤ (Real.exp R * ((2 : ℝ)^r * ((k i + 1 : ℕ) : ℝ)^r)) *
                ((R + 1)^(k i) / (Nat.factorial (k i) : ℝ)) :=
              mul_le_mul_of_nonneg_right hmain htail
          _ = Real.exp R * (2 : ℝ)^r * ((k i + 1 : ℕ) : ℝ)^r *
                (R + 1)^(k i) / (Nat.factorial (k i) : ℝ) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              ring
          _ = Real.exp R * (2 : ℝ)^r *
                (((k i + 1 : ℕ) : ℝ)^r * (R + 1)^(k i) /
                  (Nat.factorial (k i) : ℝ)) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              ring
  have hfunc : (fun z : Fin 3 → ℝ => poissonWeight (z i) (k i)) =
      (fun x : ℝ => poissonWeight x (k i)) ∘ P := rfl
  have hf : ContDiff ℝ ⊤ (fun x : ℝ => poissonWeight x (k i)) := by
    change ContDiff ℝ ⊤ (fun x : ℝ =>
      Real.exp (-x) * x^(k i) / (Nat.factorial (k i) : ℝ))
    fun_prop
  have hcomp := P.iteratedFDeriv_comp_right hf μ (i := s) (by simp)
  have hprodP : ∏ j : Fin s, ‖P‖ ≤ 1 := by
    simpa only [Finset.prod_const, Finset.card_fin] using
      (pow_le_one₀ (norm_nonneg P) hP : ‖P‖^s ≤ 1)
  calc
    ‖iteratedFDeriv ℝ s (fun z : Fin 3 → ℝ => poissonWeight (z i) (k i)) μ‖ =
        ‖(iteratedFDeriv ℝ s (fun x : ℝ => poissonWeight x (k i)) (P μ)).compContinuousLinearMap
            (fun _ : Fin s => P)‖ := by
          rw [hfunc, hcomp]
    _ ≤ ‖iteratedFDeriv ℝ s (fun x : ℝ => poissonWeight x (k i)) (P μ)‖ *
          ∏ j : Fin s, ‖P‖ := ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ s (fun x : ℝ => poissonWeight x (k i)) (P μ)‖ * 1 :=
          mul_le_mul_of_nonneg_left hprodP (norm_nonneg _)
    _ ≤ poissonCubeScale R r * poissonCubeFactor R r (k i) := by
          simpa [P] using houter

private lemma poissonMajorant_nonneg (R : ℝ) (hR : 0 ≤ R) (r : ℕ)
    (k : Fin 3 → ℕ) : 0 ≤ ThLean.BP.SA.poissonMajorant R r k := by
  unfold ThLean.BP.SA.poissonMajorant
  apply Finset.prod_nonneg
  intro i hi
  positivity

private lemma iteratedFDeriv_poissonProduct_bound (R : ℝ) (hR : 0 ≤ R) (r : ℕ)
    (k : Fin 3 → ℕ) (μ : Fin 3 → ℝ) (hμ : ∀ i, |μ i| ≤ R) :
    ‖iteratedFDeriv ℝ r
      (fun x : Fin 3 → ℝ => ∏ i : Fin 3, poissonWeight (x i) (k i)) μ‖ ≤
      (∑ p ∈ (Finset.univ : Finset (Fin 3)).sym r,
        ((p : Multiset (Fin 3)).countPerms : ℝ) * (poissonCubeScale R r)^3) *
        ThLean.BP.SA.poissonMajorant R r k := by
  have hprod := norm_iteratedFDeriv_prod_le
    (u := (Finset.univ : Finset (Fin 3)))
    (f := fun i (x : Fin 3 → ℝ) => poissonWeight (x i) (k i))
    (N := ⊤) (fun i hi => by
      change ContDiff ℝ ⊤ (fun x : Fin 3 → ℝ =>
        Real.exp (-(x i)) * (x i)^(k i) / (Nat.factorial (k i) : ℝ))
      fun_prop) (x := μ) (n := r) (by simp)
  have hterm (p : Sym (Fin 3) r) (hp : p ∈ (Finset.univ : Finset (Fin 3)).sym r) :
      ∏ i ∈ (Finset.univ : Finset (Fin 3)),
        ‖iteratedFDeriv ℝ ((p : Multiset (Fin 3)).count i)
          (fun x : Fin 3 → ℝ => poissonWeight (x i) (k i)) μ‖ ≤
      (poissonCubeScale R r)^3 * ThLean.BP.SA.poissonMajorant R r k := by
    have hcount (i : Fin 3) : (p : Multiset (Fin 3)).count i ≤ r := by
      exact (Multiset.count_le_card i _).trans_eq p.card_coe
    calc
      ∏ i ∈ (Finset.univ : Finset (Fin 3)),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin 3)).count i)
            (fun x : Fin 3 → ℝ => poissonWeight (x i) (k i)) μ‖
        ≤ ∏ i ∈ (Finset.univ : Finset (Fin 3)),
            poissonCubeScale R r * poissonCubeFactor R r (k i) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            positivity
          · intro i hi
            exact coordinatePoissonWeight_bound R hR r
              ((p : Multiset (Fin 3)).count i) (hcount i) k i μ hμ
      _ = (poissonCubeScale R r)^3 * ThLean.BP.SA.poissonMajorant R r k := by
          simp [poissonCubeScale, poissonCubeFactor, ThLean.BP.SA.poissonMajorant,
            Finset.prod_mul_distrib]
  calc
    ‖iteratedFDeriv ℝ r
        (fun x : Fin 3 → ℝ => ∏ i : Fin 3, poissonWeight (x i) (k i)) μ‖ ≤
      ∑ p ∈ (Finset.univ : Finset (Fin 3)).sym r,
        ((p : Multiset (Fin 3)).countPerms : ℝ) *
          ∏ j ∈ (Finset.univ : Finset (Fin 3)),
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin 3)).count j)
              (fun x : Fin 3 → ℝ => poissonWeight (x j) (k j)) μ‖ := by
        simpa using hprod
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin 3)).sym r,
        ((p : Multiset (Fin 3)).countPerms : ℝ) *
          ((poissonCubeScale R r)^3 * ThLean.BP.SA.poissonMajorant R r k) := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left (hterm p hp) (by positivity)
    _ = (∑ p ∈ (Finset.univ : Finset (Fin 3)).sym r,
          ((p : Multiset (Fin 3)).countPerms : ℝ) * (poissonCubeScale R r)^3) *
          ThLean.BP.SA.poissonMajorant R r k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        ring

theorem SA_I13eStatement_holds : SA_I13eStatement := by
  intro q n₁ n₂ hq hn₁ hn₂ R hR r
  refine ⟨interpolationCubeConstant R r, interpolationCubeConstant_pos R r, ?_⟩
  intro k μ hμ
  have hcoeff := interpolationCoefficient_bounds q n₁ n₂ k
  have hterm : interpolationTerm q n₁ n₂ k = fun x : Fin 3 → ℝ =>
      interpolationCoefficient q n₁ n₂ k • ∏ i : Fin 3, poissonWeight (x i) (k i) := by
    funext x
    simp [interpolationTerm, mul_comm]
  have hcont : ContDiffAt ℝ r
      (fun x : Fin 3 → ℝ => ∏ i : Fin 3, poissonWeight (x i) (k i)) μ := by
    change ContDiffAt ℝ r (fun x : Fin 3 → ℝ =>
      ∏ i : Fin 3, Real.exp (-(x i)) * (x i)^(k i) /
        (Nat.factorial (k i) : ℝ)) μ
    fun_prop
  rw [hterm]
  change ‖iteratedFDeriv ℝ r
      (interpolationCoefficient q n₁ n₂ k •
        (fun x : Fin 3 → ℝ => ∏ i : Fin 3, poissonWeight (x i) (k i))) μ‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply hcont, norm_smul]
  have hnormCoeff : ‖interpolationCoefficient q n₁ n₂ k‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hcoeff.1]
    exact hcoeff.2
  have hsum_nonneg : 0 ≤ ∑ p ∈ (Finset.univ : Finset (Fin 3)).sym r,
      ((p : Multiset (Fin 3)).countPerms : ℝ) * (poissonCubeScale R r)^3 := by
    apply Finset.sum_nonneg
    intro p hp
    have hscale : 0 ≤ poissonCubeScale R r := by
      unfold poissonCubeScale
      positivity
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hscale 3)
  have hmajorant := poissonMajorant_nonneg R hR r k
  calc
    ‖interpolationCoefficient q n₁ n₂ k‖ *
        ‖iteratedFDeriv ℝ r
          (fun x : Fin 3 → ℝ => ∏ i : Fin 3, poissonWeight (x i) (k i)) μ‖ ≤
      1 * ‖iteratedFDeriv ℝ r
          (fun x : Fin 3 → ℝ => ∏ i : Fin 3, poissonWeight (x i) (k i)) μ‖ :=
      mul_le_mul_of_nonneg_right hnormCoeff (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ r
          (fun x : Fin 3 → ℝ => ∏ i : Fin 3, poissonWeight (x i) (k i)) μ‖ := by ring
    _ ≤ (∑ p ∈ (Finset.univ : Finset (Fin 3)).sym r,
          ((p : Multiset (Fin 3)).countPerms : ℝ) * (poissonCubeScale R r)^3) *
          ThLean.BP.SA.poissonMajorant R r k :=
      iteratedFDeriv_poissonProduct_bound R hR r k μ hμ
    _ ≤ interpolationCubeConstant R r * ThLean.BP.SA.poissonMajorant R r k := by
      unfold interpolationCubeConstant
      nlinarith

end ThLean.W.SA30

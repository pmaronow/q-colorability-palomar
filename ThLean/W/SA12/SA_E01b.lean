import ThLean.BP.SA.Alternatives

noncomputable section

open scoped BigOperators Topology

namespace ThLean.W.SA12

open ThresholdFoundations

private def expTerm (μ : ℝ) (j : ℕ) : ℝ := μ ^ j / (j.factorial : ℝ)

private lemma poisson_first_succ (μ : ℝ) (j : ℕ) :
    poissonWeight μ (j + 1) * ((j + 1 : ℕ) : ℝ) =
      Real.exp (-μ) * μ * expTerm μ j := by
  simp only [poissonWeight, expTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  field_simp

private lemma poisson_factorial_succ (μ : ℝ) (j : ℕ) :
    poissonWeight μ (j + 2) * ((j + 2 : ℕ) : ℝ) *
      (((j + 2 : ℕ) : ℝ) - 1) =
      Real.exp (-μ) * μ ^ 2 * expTerm μ j := by
  simp only [poissonWeight, expTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  have hj₁ : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hj₂ : (0 : ℝ) < (j + 2 : ℕ) := by positivity
  field_simp; ring

theorem SA_E01bStatement_holds : ThLean.BP.SA.SA_E01bStatement := by
  intro μ hμ
  let a : ℕ → ℝ := expTerm μ
  let w : ℕ → ℝ := poissonWeight μ
  let C : ℝ := Real.exp (-μ)
  have ha : Summable a := by
    change Summable (fun j : ℕ => μ ^ j / (j.factorial : ℝ))
    exact Real.summable_pow_div_factorial μ
  have ha_sum : (∑' j : ℕ, a j) = Real.exp μ := by
    calc
      (∑' j : ℕ, a j) = NormedSpace.exp μ := by
        change (∑' j : ℕ, μ ^ j / (j.factorial : ℝ)) = NormedSpace.exp μ
        exact congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)).symm μ
      _ = Real.exp μ := congrFun Real.exp_eq_exp_ℝ.symm μ
  have hw_eq (j : ℕ) : w j = C * a j := by
    simp [w, C, a, expTerm, poissonWeight]
    ring
  have hw : Summable w := (ha.mul_left C).congr (fun j => (hw_eq j).symm)
  have hw_sum : (∑' j : ℕ, w j) = 1 := by
    calc
      (∑' j : ℕ, w j) = C * (∑' j : ℕ, a j) := by
        rw [show w = fun j => C * a j from funext hw_eq]
        exact ha.tsum_mul_left C
      _ = 1 := by
        rw [ha_sum]
        dsimp [C]
        rw [← Real.exp_add]
        simp

  have hfirst_point (j : ℕ) :
      w (j + 1) * ((j + 1 : ℕ) : ℝ) = (C * μ) * a j := by
    simpa [w, a, C] using (poisson_first_succ μ j)

  have hfirst_tail : Summable (fun j : ℕ => C * μ * a j) :=
    ha.mul_left (C * μ)
  have hfirst : Summable (fun j : ℕ => w j * (j : ℝ)) := by
    apply (summable_nat_add_iff (f := fun j : ℕ => w j * (j : ℝ)) 1).mp
    apply hfirst_tail.congr
    intro j
    exact (hfirst_point j).symm

  have hfirst_sum : (∑' j : ℕ, w j * (j : ℝ)) = μ := by
    calc
      (∑' j : ℕ, w j * (j : ℝ)) =
          (w 0 * (0 : ℝ)) + ∑' j : ℕ, w (j + 1) * ((j + 1 : ℕ) : ℝ) :=
        by simpa using hfirst.tsum_eq_zero_add
      _ = (C * μ) * (∑' j : ℕ, a j) := by
        rw [show (fun j : ℕ => w (j + 1) * ((j + 1 : ℕ) : ℝ)) =
          fun j => (C * μ) * a j from funext hfirst_point]
        simp only [mul_zero, zero_add]
        exact ha.tsum_mul_left (C * μ)
      _ = μ := by
        rw [ha_sum]
        dsimp [C]
        calc
          (Real.exp (-μ) * μ) * Real.exp μ =
              μ * (Real.exp (-μ) * Real.exp μ) := by ring
          _ = μ := by rw [← Real.exp_add]; simp

  have hfact_tail : Summable (fun j : ℕ => (C * μ ^ 2) * a j) :=
    ha.mul_left (C * μ ^ 2)
  have hfact : Summable (fun j : ℕ =>
      w j * (j : ℝ) * ((j : ℝ) - 1)) := by
    apply (summable_nat_add_iff (f := fun j : ℕ =>
      w j * (j : ℝ) * ((j : ℝ) - 1)) 2).mp
    apply hfact_tail.congr
    intro j
    exact (show w (j + 2) * ((j + 2 : ℕ) : ℝ) *
        (((j + 2 : ℕ) : ℝ) - 1) = (C * μ ^ 2) * a j by
          simpa [w, a, C] using (poisson_factorial_succ μ j)).symm

  have hfact_sum : (∑' j : ℕ,
      w j * (j : ℝ) * ((j : ℝ) - 1)) = μ ^ 2 := by
    have hshift := hfact.sum_add_tsum_nat_add 2
    have hsmall : (∑ j ∈ Finset.range 2,
        w j * (j : ℝ) * ((j : ℝ) - 1)) = 0 := by
      simp [Finset.sum_range_succ, w, poissonWeight]
    have htail : (∑' j : ℕ,
        w (j + 2) * ((j + 2 : ℕ) : ℝ) * (((j + 2 : ℕ) : ℝ) - 1)) =
          (C * μ ^ 2) * (∑' j : ℕ, a j) := by
      rw [show (fun j : ℕ =>
          w (j + 2) * ((j + 2 : ℕ) : ℝ) * (((j + 2 : ℕ) : ℝ) - 1)) =
          fun j => (C * μ ^ 2) * a j from funext (by
            intro j
            simpa [w, a, C] using (poisson_factorial_succ μ j))]
      exact ha.tsum_mul_left (C * μ ^ 2)
    calc
      (∑' j : ℕ, w j * (j : ℝ) * ((j : ℝ) - 1)) =
          ∑' j : ℕ, w (j + 2) * ((j + 2 : ℕ) : ℝ) *
            (((j + 2 : ℕ) : ℝ) - 1) := by
        have h := hshift
        rw [hsmall] at h
        simpa using h.symm
      _ = (C * μ ^ 2) * (∑' j : ℕ, a j) := htail
      _ = μ ^ 2 := by
        rw [ha_sum]
        dsimp [C]
        calc
          (Real.exp (-μ) * μ ^ 2) * Real.exp μ =
              μ ^ 2 * (Real.exp (-μ) * Real.exp μ) := by ring
          _ = μ ^ 2 := by rw [← Real.exp_add]; simp

  have hsecond : Summable (fun j : ℕ => w j * (j : ℝ) ^ 2) := by
    have h := hfact.add hfirst
    apply h.congr
    intro j
    dsimp [w]
    ring

  have hsecond_sum : (∑' j : ℕ, w j * (j : ℝ) ^ 2) = μ ^ 2 + μ := by
    have hpoint : (fun j : ℕ => w j * (j : ℝ) ^ 2) =
        fun j => (w j * (j : ℝ) * ((j : ℝ) - 1)) + w j * (j : ℝ) := by
      funext j
      ring
    rw [hpoint, hfact.tsum_add hfirst, hfact_sum, hfirst_sum]

  have hcenter : Summable (fun j : ℕ => w j * ((j : ℝ) - μ) ^ 2) := by
    have hlin : Summable (fun j : ℕ =>
        (w j * (j : ℝ) ^ 2 - (2 * μ) * (w j * (j : ℝ))) + μ ^ 2 * w j) :=
      (hsecond.sub (hfirst.mul_left (2 * μ))).add (hw.mul_left (μ ^ 2))
    apply hlin.congr
    intro j
    ring

  have hcenter_sum : (∑' j : ℕ, w j * ((j : ℝ) - μ) ^ 2) = μ := by
    have hpoint : (fun j : ℕ => w j * ((j : ℝ) - μ) ^ 2) =
        fun j => (w j * (j : ℝ) ^ 2 - (2 * μ) * (w j * (j : ℝ))) + μ ^ 2 * w j := by
      funext j
      ring
    rw [hpoint]
    rw [(hsecond.sub (hfirst.mul_left (2 * μ))).tsum_add (hw.mul_left (μ ^ 2))]
    rw [hsecond.tsum_sub (hfirst.mul_left (2 * μ))]
    rw [hfirst.tsum_mul_left (2 * μ)]
    rw [hw.tsum_mul_left (μ ^ 2)]
    rw [hsecond_sum, hfirst_sum, hw_sum]
    ring

  exact ⟨hfirst, hsecond, hfirst_sum, hfact_sum, hsecond_sum, hcenter_sum⟩

end ThLean.W.SA12

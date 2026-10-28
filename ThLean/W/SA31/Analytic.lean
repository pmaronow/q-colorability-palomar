import ThLean.BP.SA.Analytic

noncomputable section
open scoped BigOperators

namespace ThLean.W.SA31

private def poissonFactor (R : ℝ) (r n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ r * (R + 1) ^ n / (Nat.factorial n : ℝ)

private lemma poissonFactor_nonneg (R : ℝ) (hR : 0 ≤ R) (r n : ℕ) :
    0 ≤ poissonFactor R r n := by
  unfold poissonFactor
  positivity

private lemma poissonFactor_summable (R : ℝ) (hR : 0 ≤ R) (r : ℕ) :
    Summable (poissonFactor R r) := by
  have hn : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hp : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ^ r ≤ (2 ^ r : ℝ) ^ n := by
    intro n
    have hn' : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hn n
    calc
      ((n + 1 : ℕ) : ℝ) ^ r ≤ ((2 : ℝ) ^ n) ^ r := by gcongr
      _ = ((2 : ℝ) ^ r) ^ n := by
        calc
          ((2 : ℝ) ^ n) ^ r = (2 : ℝ) ^ (n * r) := by rw [pow_mul]
          _ = (2 : ℝ) ^ (r * n) := by rw [Nat.mul_comm]
          _ = ((2 : ℝ) ^ r) ^ n := by rw [pow_mul]
  have hs := Real.summable_pow_div_factorial ((2 : ℝ) ^ r * (R + 1))
  apply Summable.of_nonneg_of_le (fun n => poissonFactor_nonneg R hR r n)
  · intro n
    have ht : 0 ≤ R + 1 := by linarith
    have hnum : (((n + 1 : ℕ) : ℝ) ^ r) * (R + 1) ^ n ≤
        ((2 : ℝ) ^ r) ^ n * (R + 1) ^ n :=
      mul_le_mul_of_nonneg_right (hp n) (pow_nonneg ht n)
    unfold poissonFactor
    calc
      (((n + 1 : ℕ) : ℝ) ^ r * (R + 1) ^ n / (Nat.factorial n : ℝ))
          ≤ ((2 : ℝ) ^ r) ^ n * (R + 1) ^ n / (Nat.factorial n : ℝ) :=
            div_le_div_of_nonneg_right hnum (by positivity)
      _ = (((2 : ℝ) ^ r * (R + 1)) ^ n) / (Nat.factorial n : ℝ) := by rw [mul_pow]
  · exact hs

theorem SA_I13fStatement_holds : ThLean.BP.SA.SA_I13fStatement := by
  intro R hR r
  have hs := poissonFactor_summable R hR r
  have hn : ∀ n, 0 ≤ poissonFactor R r n := fun n => poissonFactor_nonneg R hR r n
  have h2 : Summable (fun p : ℕ × ℕ => poissonFactor R r p.1 * poissonFactor R r p.2) :=
    hs.mul_of_nonneg hs hn hn
  have h3 : Summable
      (fun p : (ℕ × ℕ) × ℕ =>
        poissonFactor R r p.1.1 * poissonFactor R r p.1.2 * poissonFactor R r p.2) :=
    h2.mul_of_nonneg hs (fun p => mul_nonneg (hn p.1) (hn p.2)) hn
  let e : (Fin 3 → ℕ) ≃ (ℕ × ℕ) × ℕ := {
    toFun f := ((f 0, f 1), f 2)
    invFun p := fun i => if i = 0 then p.1.1 else if i = 1 then p.1.2 else p.2
    left_inv f := by funext i; fin_cases i <;> simp
    right_inv p := by rcases p with ⟨⟨a, b⟩, c⟩; rfl
  }
  have hmajor : Summable (fun k : Fin 3 → ℕ => ∏ i : Fin 3, poissonFactor R r (k i)) := by
    have hh := h3.comp_injective e.injective
    change Summable (fun k : Fin 3 → ℕ =>
      poissonFactor R r (k 0) * poissonFactor R r (k 1) * poissonFactor R r (k 2)) at hh
    simpa [Fin.prod_univ_three] using hh
  change Summable (fun k : Fin 3 → ℕ => ∏ i : Fin 3, poissonFactor R r (k i))
  exact hmajor

end ThLean.W.SA31

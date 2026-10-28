import ThLean.BP.S4.Reduction

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S440

open ThresholdFoundations ThLean.BP.S4

private theorem uniformMean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_add_distrib]
  ring

private theorem uniformMean_smul {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

private theorem terminalReal_add {V : Type} [Fintype V] (q L U : ℕ)
    (F J : ℕ → MGraph V → Pair V → ℝ) :
    terminalReal q L U (fun h G e => F h G e + J h G e) =
      terminalReal q L U F + terminalReal q L U J := by
  classical
  unfold terminalReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hpoint (x : EdgeTuple V k) :
      uniformMean (fun e : Pair V =>
        if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
        then F (k+1) (tupleGraph x) e + J (k+1) (tupleGraph x) e else 0) =
      uniformMean (fun e : Pair V =>
        if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
        then F (k+1) (tupleGraph x) e else 0) +
      uniformMean (fun e : Pair V =>
        if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
        then J (k+1) (tupleGraph x) e else 0) := by
    have hfun :
        (fun e : Pair V =>
          if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
          then F (k+1) (tupleGraph x) e + J (k+1) (tupleGraph x) e else 0) =
        (fun e : Pair V =>
          (if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
           then F (k+1) (tupleGraph x) e else 0) +
          (if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
           then J (k+1) (tupleGraph x) e else 0)) := by
      funext e
      by_cases he : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e) <;>
        simp [he]
    rw [hfun, uniformMean_add]
  rw [← uniformMean_add]
  apply congrArg uniformMean
  funext x
  exact hpoint x

private theorem terminalReal_smul {V : Type} [Fintype V] (q L U : ℕ)
    (c : ℝ) (F : ℕ → MGraph V → Pair V → ℝ) :
    terminalReal q L U (fun h G e => c * F h G e) = c * terminalReal q L U F := by
  classical
  unfold terminalReal
  calc
    (∑ k ∈ Finset.Ico L U,
        uniformMean (fun x : EdgeTuple V k => uniformMean (fun e : Pair V =>
          if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
          then c * F (k+1) (tupleGraph x) e else 0))) =
      ∑ k ∈ Finset.Ico L U, c * uniformMean (fun x : EdgeTuple V k =>
        uniformMean (fun e : Pair V =>
          if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
          then F (k+1) (tupleGraph x) e else 0)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hinner (x : EdgeTuple V k) :
            uniformMean (fun e : Pair V =>
              if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
              then c * F (k+1) (tupleGraph x) e else 0) =
            c * uniformMean (fun e : Pair V =>
              if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
              then F (k+1) (tupleGraph x) e else 0) := by
          have hfun :
              (fun e : Pair V =>
                if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
                then c * F (k+1) (tupleGraph x) e else 0) =
              (fun e : Pair V => c *
                (if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
                 then F (k+1) (tupleGraph x) e else 0)) := by
            funext e
            by_cases he : Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e) <;>
              simp [he]
          rw [hfun, uniformMean_smul]
        have hfun :
            (fun x : EdgeTuple V k => uniformMean (fun e : Pair V =>
              if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
              then c * F (k+1) (tupleGraph x) e else 0)) =
            (fun x => c * uniformMean (fun e : Pair V =>
              if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
              then F (k+1) (tupleGraph x) e else 0)) := by
          funext x
          exact hinner x
        rw [hfun, uniformMean_smul]
    _ = c * (∑ k ∈ Finset.Ico L U,
        uniformMean (fun x : EdgeTuple V k => uniformMean (fun e : Pair V =>
          if Colorable q (tupleGraph x) ∧ ¬ Colorable q (addPair (tupleGraph x) e)
          then F (k+1) (tupleGraph x) e else 0))) := by
        rw [Finset.mul_sum]

private theorem terminalReal_const {V : Type} [Fintype V] (q L U : ℕ) (c : ℝ) :
    terminalReal q L U (fun (_ : ℕ) (_ : MGraph V) (_ : Pair V) => c) =
      c * terminalProb (V := V) q L U (fun (_ : MGraph V) (_ : Pair V) => True) := by
  calc
    terminalReal q L U (fun (_ : ℕ) (_ : MGraph V) (_ : Pair V) => c) =
        c * terminalReal q L U (fun (_ : ℕ) (_ : MGraph V) (_ : Pair V) => (1 : ℝ)) := by
          simpa using terminalReal_smul q L U c
            (fun (_ : ℕ) (_ : MGraph V) (_ : Pair V) => (1 : ℝ))
    _ = c * terminalProb (V := V) q L U (fun (_ : MGraph V) (_ : Pair V) => True) := by
          simp [terminalProb, indicator]

theorem S4_RED_15BStatement_of_deps
    (halg : S4_ALG_01Statement)
    (hbridge : S4_BRIDGE_01CStatement) :
    S4_RED_15BStatement := by
  intro q n hq hn L U hLU s ε hs hε B hB hnotB
  let tail : MGraph (Fin n) → Pair (Fin n) → Prop :=
    fun G e => s * ε ^ 2 < lifetimeReal q G
  let P : MGraph (Fin n) → Pair (Fin n) → Prop := fun G e => tail G e ∧ B G e
  let Q : MGraph (Fin n) → Pair (Fin n) → Prop := fun G e => tail G e ∧ ¬ B G e
  let F : ℕ → MGraph (Fin n) → Pair (Fin n) → ℝ :=
    fun _ G _ => min (s * ε) (lifetimeReal q G)
  let J : ℕ → MGraph (Fin n) → Pair (Fin n) → ℝ :=
    fun _ G e => s * ε ^ 2 + (s * ε) * indicator (tail G e)
  have ha : 0 ≤ s * ε := le_of_lt (mul_pos hs hε)
  have hx : 0 ≤ s * ε ^ 2 := mul_nonneg (le_of_lt hs) (sq_nonneg ε)
  have hy (G : MGraph (Fin n)) : 0 ≤ lifetimeReal q G := ENNReal.toReal_nonneg
  have hterm : terminalReal q L U F ≤ terminalReal q L U J := by
    apply (hbridge q n hq hn L U hLU).2.2 F J
    intro h G e hL hU hLoop hColor hFail
    exact halg.2 (s * ε) (s * ε ^ 2) (lifetimeReal q G) ha hx (hy G)
  have hsplit : terminalProb q L U tail =
      terminalProb q L U P + terminalProb q L U Q := by
    unfold terminalProb
    have hfun : (fun (_ : ℕ) (G : MGraph (Fin n)) (e : Pair (Fin n)) =>
        indicator (tail G e)) = (fun _ G e => indicator (P G e) + indicator (Q G e)) := by
      funext _ G e
      by_cases ht : tail G e
      · by_cases hb : B G e <;> simp [P, Q, ht, hb, indicator]
      · simp [P, Q, ht, indicator]
    rw [hfun, terminalReal_add]
  have hJ : terminalReal q L U J =
      (s * ε ^ 2) * terminalProb (V := Fin n) q L U (fun _ _ => True) +
        (s * ε) * terminalProb q L U tail := by
    dsimp [J]
    rw [terminalReal_add, terminalReal_const, terminalReal_smul]
    simp [terminalProb, indicator]
  have hmass : terminalProb (V := Fin n) q L U (fun _ _ => True) ≤ 1 :=
    (hbridge q n hq hn L U hLU).1
  have htail : terminalProb q L U tail ≤ ε + ε := by
    rw [hsplit]
    exact add_le_add hB hnotB
  have hbound :
      (s * ε ^ 2) * terminalProb (V := Fin n) q L U (fun _ _ => True) +
        (s * ε) * terminalProb q L U tail ≤ 3 * s * ε ^ 2 := by
    calc
      (s * ε ^ 2) * terminalProb (V := Fin n) q L U (fun _ _ => True) +
          (s * ε) * terminalProb q L U tail ≤
        (s * ε ^ 2) * 1 + (s * ε) * (ε + ε) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hmass hx
          · exact mul_le_mul_of_nonneg_left htail ha
      _ = 3 * s * ε ^ 2 := by ring
  calc
    cappedMoment q n L U (s * ε) = terminalReal q L U F := rfl
    _ ≤ terminalReal q L U J := hterm
    _ ≤ 3 * s * ε ^ 2 := by rw [hJ]; exact hbound

example (halg : S4_ALG_01Statement) (hbridge : S4_BRIDGE_01CStatement) :
    S4_RED_15BStatement := S4_RED_15BStatement_of_deps halg hbridge

end ThLean.W.S440

module

public import ThLean.BP.S6.Main

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S643

private theorem indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  by_cases h : P <;> simp [indicator, h]

theorem S6_40Statement_of_deps
    (h01 : ThLean.BP.S6.S6_01aStatement)
    (h05 : ThLean.BP.S6.S6_05Statement)
    (h08 : ThLean.BP.S6.S6_08Statement)
    (h12 : ThLean.BP.S6.S6_12Statement)
    (h14 : ThLean.BP.S6.S6_14Statement)
    (h15 : ThLean.BP.S6.S6_15Statement)
    (h33 : ThLean.BP.S6.S6_33Statement) :
    ThLean.BP.S6.S6_40Statement := by
  classical
  intro n q Λ hn hq hΛ w u hcut
  let M := cap Λ n
  let K := pivotalCut Λ
  have hp := h33 n Λ hn hΛ
  have hKw : K ≤ w := by simpa [K] using hcut
  have hKpos : 1 ≤ K := hp.Kpos
  have hbeta_nonneg (G : Graph n) : 0 ≤ beta q G u :=
    (h05 n q hn hq G u).2.2.2.2.2.1
  have hrootEq_nonneg (t r : ℕ) : 0 ≤ rootEqMean n q t r u := by
    change 0 ≤ uniformMean (fun x : Hist n t =>
      indicator (degree (tupleGraph x) u = r) * beta q (tupleGraph x) u)
    exact (h01 (Hist n t)).nonneg _ (fun x =>
      mul_nonneg (indicator_nonneg _) (hbeta_nonneg (tupleGraph x)))
  have hrootGe_nonneg (t : ℕ) : 0 ≤ rootGeMean n q t w u := by
    change 0 ≤ uniformMean (fun x : Hist n t =>
      indicator (w ≤ degree (tupleGraph x) u) * beta q (tupleGraph x) u)
    exact (h01 (Hist n t)).nonneg _ (fun x =>
      mul_nonneg (indicator_nonneg _) (hbeta_nonneg (tupleGraph x)))
  have hmean_sum (t : ℕ) (s : Finset ℕ) (f : ℕ → Hist n t → ℝ) :
      uniformMean (fun x : Hist n t => ∑ r ∈ s, f r x) =
        ∑ r ∈ s, uniformMean (f r) := by
    induction s using Finset.induction_on with
    | empty => simp [uniformMean]
    | @insert a s has ih =>
      simp only [Finset.sum_insert has]
      rw [(h01 (Hist n t)).add, ih]
  have hedgeCount (t : ℕ) (x : Hist n t) :
      edgeCount (tupleGraph x) = t := by
    letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    unfold edgeCount tupleGraph
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    change (∑ i : Fin t, ∑ e : Sym2 (Fin n),
      if (x i).val = e then 1 else 0) = t
    simp only [Fintype.sum_ite_eq]
    simp
  have hdegree_le (t : ℕ) (x : Hist n t) :
      degree (tupleGraph x) u ≤ t := by
    have hle : degree (tupleGraph x) u ≤ edgeCount (tupleGraph x) := by
      unfold degree edgeCount
      apply Finset.sum_le_sum
      intro e _
      by_cases he : Touches u e <;> simp [he]
    exact hle.trans (by rw [hedgeCount])
  have hpartition (t : ℕ) :
      (∑ r ∈ Finset.Ico w (t + 1), rootEqMean n q t r u) =
        rootGeMean n q t w u := by
    have hsumIndicator (x : Hist n t) :
        (∑ r ∈ Finset.Ico w (t + 1),
          indicator (degree (tupleGraph x) u = r)) =
            indicator (w ≤ degree (tupleGraph x) u) := by
      have hdt : degree (tupleGraph x) u ≤ t := hdegree_le t x
      by_cases hw : w ≤ degree (tupleGraph x) u
      · have hmem : degree (tupleGraph x) u ∈ Finset.Ico w (t + 1) := by
          simp only [Finset.mem_Ico]
          omega
        rw [Finset.sum_eq_single (degree (tupleGraph x) u)]
        · simp [indicator, hw]
        · intro r hr hrd
          have hne : ¬ degree (tupleGraph x) u = r := by
            intro heq
            exact hrd heq.symm
          simp [indicator, hne]
        · intro hnot
          exact False.elim (hnot hmem)
      · rw [Finset.sum_eq_zero]
        · simp [indicator, hw]
        · intro r hr
          have hne : ¬ degree (tupleGraph x) u = r := by
            intro heq
            subst r
            exact hw (Finset.mem_Ico.mp hr).1
          simp [indicator, hne]
    change (∑ r ∈ Finset.Ico w (t + 1),
        uniformMean (fun x : Hist n t =>
          indicator (degree (tupleGraph x) u = r) * beta q (tupleGraph x) u)) =
      uniformMean (fun x : Hist n t =>
        indicator (w ≤ degree (tupleGraph x) u) * beta q (tupleGraph x) u)
    rw [← hmean_sum t (Finset.Ico w (t + 1))
      (fun r x => indicator (degree (tupleGraph x) u = r) * beta q (tupleGraph x) u)]
    congr 1
    funext x
    rw [← Finset.sum_mul, hsumIndicator x]
  have hreindex (f : ℕ → ℕ → ℝ) :
      (∑ j ∈ Finset.Ico (w + 1) M, ∑ m ∈ Finset.Ico j M,
        f (m - 1) (j - 1)) =
        ∑ t ∈ Finset.Ico w (M - 1), ∑ r ∈ Finset.Ico w (t + 1), f t r := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    let forward : (Σ j : ℕ, ℕ) → (Σ t : ℕ, ℕ) :=
      fun p => ⟨p.2 - 1, p.1 - 1⟩
    let backward : (Σ t : ℕ, ℕ) → (Σ j : ℕ, ℕ) :=
      fun p => ⟨p.2 + 1, p.1 + 1⟩
    refine Finset.sum_bij'
      (fun p _ => forward p) (fun p _ => backward p) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨hpj, hpm⟩
      simp only [Finset.mem_Ico] at hpj hpm
      simp only [Finset.mem_sigma, Finset.mem_Ico]
      dsimp [forward]
      omega
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨hpt, hpr⟩
      simp only [Finset.mem_Ico] at hpt hpr
      simp only [Finset.mem_sigma, Finset.mem_Ico]
      dsimp [backward]
      omega
    · intro p hp
      rcases p with ⟨j, m⟩
      rcases Finset.mem_sigma.mp hp with ⟨hpj, hpm⟩
      simp only [Finset.mem_Ico] at hpj hpm
      dsimp [forward, backward] <;> (congr 1 <;> omega)
    · intro p hp
      rcases p with ⟨t, r⟩
      rcases Finset.mem_sigma.mp hp with ⟨hpt, hpr⟩
      simp only [Finset.mem_Ico] at hpt hpr
      dsimp [forward, backward]
    · intro p hp
      rfl
  let C : ℝ := (2 * Λ / ((w - K + 2 : ℕ) : ℝ)) *
    ((n : ℝ) / ((n : ℝ) - 1)) ^ 2
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hn1 : 0 < (n : ℝ) - 1 := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hwdenNat : 0 < w - K + 2 := by omega
  have hwden : 0 < ((w - K + 2 : ℕ) : ℝ) := by exact_mod_cast hwdenNat
  have hcoef (j m : ℕ) (hj : j ∈ Finset.Ico (w + 1) M)
      (hm : m ∈ Finset.Ico j M) :
      (2 * (m : ℝ) * (n : ℝ)) /
          (((n : ℝ) - 1) ^ 2 * ((j - K + 1 : ℕ) : ℝ)) ≤ C := by
    have hj' := Finset.mem_Ico.mp hj
    have hm' := Finset.mem_Ico.mp hm
    have hjK : K ≤ j := by omega
    have hjd : w - K + 2 ≤ j - K + 1 := by omega
    have hmM : m ≤ M := Nat.le_of_lt hm'.2
    have hmR : (m : ℝ) ≤ Λ * n := by
      have hM : (M : ℝ) ≤ Λ * n := by simpa [M] using hp.cap_le
      exact (Nat.cast_le.mpr hmM).trans hM
    let dj : ℝ := ((j - K + 1 : ℕ) : ℝ)
    let dw : ℝ := ((w - K + 2 : ℕ) : ℝ)
    let z : ℝ := ((n : ℝ) - 1) ^ 2
    have hdj : 0 < dj := by
      dsimp [dj]
      exact_mod_cast (show 0 < j - K + 1 by omega)
    have hdw_le_dj : dw ≤ dj := by
      dsimp [dj, dw]
      exact_mod_cast hjd
    have hz : 0 < z := by dsimp [z]; positivity
    have hnum : 2 * (m : ℝ) * (n : ℝ) ≤ 2 * Λ * (n : ℝ) ^ 2 := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hmR hn0
      nlinarith
    have hcore :
        (2 * (m : ℝ) * (n : ℝ)) * dw ≤
          (2 * Λ * (n : ℝ) ^ 2) * dj := by
      exact mul_le_mul hnum hdw_le_dj (le_of_lt hwden) (by positivity)
    have hcross :
        (2 * (m : ℝ) * (n : ℝ)) * (dw * z) ≤
          (2 * Λ * (n : ℝ) ^ 2) * (dj * z) := by
      calc
        _ = ((2 * (m : ℝ) * (n : ℝ)) * dw) * z := by ring
        _ ≤ ((2 * Λ * (n : ℝ) ^ 2) * dj) * z :=
          mul_le_mul_of_nonneg_right hcore (le_of_lt hz)
        _ = _ := by ring
    have hrat :
        (2 * (m : ℝ) * (n : ℝ)) / (dj * z) ≤
          (2 * Λ * (n : ℝ) ^ 2) / (dw * z) :=
      (div_le_div_iff₀ (mul_pos hdj hz) (mul_pos hwden hz)).2 hcross
    calc
      (2 * (m : ℝ) * (n : ℝ)) /
          (((n : ℝ) - 1) ^ 2 * ((j - K + 1 : ℕ) : ℝ)) =
            (2 * (m : ℝ) * (n : ℝ)) / (dj * z) := by
              congr 1
              simp [dj, z, mul_comm]
      _ ≤ (2 * Λ * (n : ℝ) ^ 2) / (dw * z) := hrat
      _ = C := by
        dsimp [C, dw, z]
        field_simp [ne_of_gt hwden, ne_of_gt hn1]
  have hpoint (j m : ℕ) (hj : j ∈ Finset.Ico (w + 1) M)
      (hm : m ∈ Finset.Ico j M) :
      pivMean n q m K j ≤ C * rootEqMean n q (m - 1) (j - 1) u := by
    have hj' := Finset.mem_Ico.mp hj
    have hm' := Finset.mem_Ico.mp hm
    have hjK : K ≤ j := by omega
    have hdel :=
      (ThLean.BP.S6.S6_16_assembly h01 h08 h12 h14 h15)
        n q m j K hn hq (by omega) hKpos hjK u
    exact hdel.trans (mul_le_mul_of_nonneg_right (hcoef j m hj hm)
      (hrootEq_nonneg (m - 1) (j - 1)))
  have hpointSum :
      (∑ j ∈ Finset.Ico (w + 1) M, ∑ m ∈ Finset.Ico j M,
        pivMean n q m K j) ≤
      C * (∑ j ∈ Finset.Ico (w + 1) M, ∑ m ∈ Finset.Ico j M,
        rootEqMean n q (m - 1) (j - 1) u) := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico (w + 1) M, ∑ m ∈ Finset.Ico j M,
            C * rootEqMean n q (m - 1) (j - 1) u := by
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum
          intro m hm
          exact hpoint j m hj hm
      _ = C * (∑ j ∈ Finset.Ico (w + 1) M,
            ∑ m ∈ Finset.Ico j M, rootEqMean n q (m - 1) (j - 1) u) := by
          symm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
  have hrootTotal :
      (∑ j ∈ Finset.Ico (w + 1) M, ∑ m ∈ Finset.Ico j M,
        rootEqMean n q (m - 1) (j - 1) u) ≤
      ∑ t ∈ Finset.range M, rootGeMean n q t w u := by
    rw [hreindex (fun t r => rootEqMean n q t r u)]
    calc
      (∑ t ∈ Finset.Ico w (M - 1),
        ∑ r ∈ Finset.Ico w (t + 1), rootEqMean n q t r u) ≤
        ∑ t ∈ Finset.Ico w (M - 1), rootGeMean n q t w u := by
          apply Finset.sum_le_sum
          intro t ht
          exact le_of_eq (hpartition t)
      _ ≤ ∑ t ∈ Finset.range M, rootGeMean n q t w u := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro t ht
            simp only [Finset.mem_Ico, Finset.mem_range] at ht ⊢
            omega
          · intro t ht ht'
            exact hrootGe_nonneg t
  change
    (∑ j ∈ Finset.Ico (w + 1) M, ∑ m ∈ Finset.Ico j M,
      pivMean n q m K j) ≤
    C * ∑ t ∈ Finset.range M, rootGeMean n q t w u
  exact hpointSum.trans (mul_le_mul_of_nonneg_left hrootTotal hCnonneg)

example
    (h01 : ThLean.BP.S6.S6_01aStatement)
    (h05 : ThLean.BP.S6.S6_05Statement)
    (h08 : ThLean.BP.S6.S6_08Statement)
    (h12 : ThLean.BP.S6.S6_12Statement)
    (h14 : ThLean.BP.S6.S6_14Statement)
    (h15 : ThLean.BP.S6.S6_15Statement)
    (h33 : ThLean.BP.S6.S6_33Statement) :
    ThLean.BP.S6.S6_40Statement :=
  S6_40Statement_of_deps h01 h05 h08 h12 h14 h15 h33

end ThLean.W.S643

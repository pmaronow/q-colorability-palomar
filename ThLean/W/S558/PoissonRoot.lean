module

public import ThLean.BP.S5.Poisson

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S558
open ThresholdFoundations
open ThLean.BP.S5

private theorem uniformMean_abs_le {A : Type} [Fintype A] [Nonempty A]
    (C : ℝ) (u : A → ℝ) (hu : ∀ a, |u a| ≤ C) :
    |uniformMean u| ≤ C := by
  have hcard : 0 < (Fintype.card A : ℝ) := by positivity
  unfold uniformMean
  rw [abs_div, abs_of_pos hcard]
  have hsum : |∑ a : A, u a| ≤ ∑ a : A, C := by
    calc
      |∑ a : A, u a| ≤ ∑ a : A, |u a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : A, C := Finset.sum_le_sum fun a _ => hu a
  calc
    |∑ a : A, u a| / (Fintype.card A : ℝ) ≤
        (∑ a : A, C) / (Fintype.card A : ℝ) := div_le_div_of_nonneg_right hsum hcard.le
    _ = C := by simp [hcard.ne']

private theorem poissonWeight_hasSum_one (z : ℝ) :
    HasSum (poissonWeight z) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp (z : ℝ)).mul_left (Real.exp (-z)) using 1
  · funext j
    simp [poissonWeight, mul_div_assoc]
  · simp [← Real.exp_eq_exp_ℝ, ← Real.exp_add]

private theorem poissonMixture_abs_le_of_abs_le {z C : ℝ} (hz : 0 ≤ z)
    (a : ℕ → ℝ) (ha : ∀ j, |a j| ≤ C) :
    |poissonMixture z a| ≤ C := by
  have hw0 : ∀ j, 0 ≤ poissonWeight z j := by
    intro j
    simp [poissonWeight]
    positivity
  have hw := poissonWeight_hasSum_one z
  have hdom : ∀ j, ‖poissonWeight z j * a j‖ ≤ C * poissonWeight z j := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 j)]
    calc
      poissonWeight z j * |a j| ≤ poissonWeight z j * C :=
        mul_le_mul_of_nonneg_left (ha j) (hw0 j)
      _ = C * poissonWeight z j := mul_comm _ _
  have hnorm := tsum_of_norm_bounded (hw.mul_left C) hdom
  simpa [poissonMixture, Real.norm_eq_abs] using hnorm

private theorem poissonRoot_parameters (n rate s : ℝ) (hn : 2 ≤ n) :
    ((n - 1) / (n + 1)) * (rate * (n * (n + 1) / 2) * s) =
        rate * (n * (n - 1) / 2) * s ∧
    2 * (rate * (n * (n + 1) / 2) * s) / (n + 1) = rate * n * s ∧
    (rate * (n * (n - 1) / 2) * s) / (n * (n - 1) / 2) = rate * s := by
  have hn1 : n + 1 ≠ 0 := by linarith
  have hnsub : 0 < n - 1 := by linarith
  have hpair : n * (n - 1) / 2 ≠ 0 := by
    have : 0 < n * (n - 1) / 2 := by positivity
    linarith
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp

theorem S5_15AStatement_of_deps
    (h08b : ThLean.BP.S5.S5_08BStatement)
    (h09b : ThLean.BP.S5.S5_09BStatement) :
    ThLean.BP.S5.S5_15AStatement := by
  intro V instV hV rate s hrate hs f hf
  let n : ℝ := Fintype.card V
  let pairs : ℝ := ((Fintype.card V).choose 2 : ℝ)
  let allPairs : ℝ := ((Fintype.card V + 1).choose 2 : ℝ)
  let bgTime : ℝ := rate * pairs * s
  let totalTime : ℝ := rate * allPairs * s
  let listTime : ℝ := rate * (Fintype.card V : ℝ) * s
  let g : MGraph V → ℝ := fun B =>
    poissonMixture listTime (fun j => listMean j (fun xs => f (addRoot B xs)))
  have hn : 2 ≤ n := by
    dsimp [n]
    exact_mod_cast hV
  have hn1 : 0 < n + 1 := by linarith
  have hpair_cast : pairs = n * (n - 1) / 2 := by
    dsimp [pairs, n]
    rw [Nat.cast_choose_two]
  have hall_cast : allPairs = n * (n + 1) / 2 := by
    dsimp [allPairs, n]
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hparams := poissonRoot_parameters n rate s hn
  have hbg_eq : bgTime = rate * (n * (n - 1) / 2) * s := by
    dsimp [bgTime]
    rw [hpair_cast]
  have htotal_eq : totalTime = rate * (n * (n + 1) / 2) * s := by
    dsimp [totalTime]
    rw [hall_cast]
  have htime_change : ((n - 1) / (n + 1)) * totalTime = bgTime := by
    rw [htotal_eq, hbg_eq]
    exact hparams.1
  have hlist_rate : 2 * totalTime / (n + 1) = listTime := by
    rw [htotal_eq]
    simpa [listTime, n] using hparams.2.1
  have hbg_nonneg : 0 ≤ bgTime := by
    dsimp [bgTime]
    positivity
  have htotal_nonneg : 0 ≤ totalTime := by
    dsimp [totalTime]
    positivity
  have hlist_nonneg : 0 ≤ listTime := by
    dsimp [listTime]
    positivity
  have hbound : ∃ C : ℝ, ∀ G : MGraph V, |g G| ≤ C := by
    rcases hf with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro B
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    apply poissonMixture_abs_le_of_abs_le hlist_nonneg
    intro j
    simpa [listMean] using
      (uniformMean_abs_le C (fun x : Fin j → V => f (addRoot B (List.ofFn x)))
        (fun x => hC (addRoot B (List.ofFn x))))
  have h08 := h08b V hV bgTime hbg_nonneg g hbound
  have h09 := h09b V hV totalTime htotal_nonneg f hf
  have hdivide : bgTime / pairs = rate * s := by
    rw [hbg_eq, hpair_cast]
    exact hparams.2.2
  rw [hdivide] at h08
  rw [hlist_rate] at h09
  have htime_coeff :
      ((Fintype.card V : ℝ) - 1) / ((Fintype.card V : ℝ) + 1) * totalTime = bgTime := by
    change ((n - 1) / (n + 1)) * totalTime = bgTime
    exact htime_change
  rw [htime_coeff] at h09
  calc
    countMean (rate * s) g = poissonGraphMean bgTime g := h08.symm
    _ = poissonGraphMean totalTime f := h09.symm

end ThLean.W.S558

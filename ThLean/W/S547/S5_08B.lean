import ThLean.W.S547.S5_08BHelpers

set_option maxHeartbeats 600000

noncomputable section
open scoped BigOperators ENNReal

namespace ThLean.W.S547

open ThresholdFoundations
open ThLean.BP.S5

theorem S5_08BStatement_of_deps
    (hPreSplit : ThresholdFoundations.PreSplitStatement.{0, 0})
    (hE01 : ThLean.BP.S5.S5_E01Statement)
    (hE08 : ThLean.BP.S5.S5_E08Statement) :
    ThLean.BP.S5.S5_08BStatement := by
  classical
  intro V instV hV t ht f hf
  letI := instV
  have hpairCard : Fintype.card (Pair V) = (Fintype.card V).choose 2 :=
    pair_card_eq_choose_two V
  have hpairPos : 0 < Fintype.card (Pair V) := by
    rw [hpairCard]
    exact Nat.choose_pos (by omega)
  letI : Nonempty (Pair V) := Fintype.card_pos_iff.mp hpairPos
  obtain ⟨C, hBound⟩ := hf
  have hC : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hBound 0)
  let fp : MGraph V → ℝ := fun G => max (f G) 0
  let fn : MGraph V → ℝ := fun G => max (-f G) 0
  have hfp0 : ∀ G, 0 ≤ fp G := fun G => le_max_right _ _
  have hfn0 : ∀ G, 0 ≤ fn G := fun G => le_max_right _ _
  have hfpC : ∀ G, fp G ≤ C := by
    intro G
    apply max_le
    · exact le_trans (le_abs_self (f G)) (hBound G)
    · exact hC
  have hfnC : ∀ G, fn G ≤ C := by
    intro G
    apply max_le
    · calc
        -f G ≤ abs (-f G) := le_abs_self _
        _ = abs (f G) := abs_neg _
        _ ≤ C := hBound G
    · exact hC
  have hdecomp (G : MGraph V) : f G = fp G - fn G := by
    by_cases h : 0 ≤ f G
    · simp [fp, fn, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · have hlt : f G < 0 := lt_of_not_ge h
      simp [fp, fn, max_eq_right (le_of_lt hlt),
        max_eq_left (neg_nonneg.mpr (le_of_lt hlt))]
  have hRate := looplessRate_eq_perPairRate t hV
  have hPoissonOne := poissonGraphMeanENN_one hV hE01 t ht
  have hTotal :
      independentPoissonGraphMeanENN (looplessRate t)
        (fun _ : MGraph V => (1 : ℝ≥0∞)) = 1 := by
    have h := hPreSplit.2.2.2 V hV t (fun _ => (1 : ℝ≥0∞)) ht
    rw [hPoissonOne] at h
    exact h.symm
  have hMass0 : ∀ G : MGraph V, 0 ≤ independentPoissonGraphMass (looplessRate t) G :=
    looplessGraphMass_nonneg (V := V) hE01 t ht
  have hPoissonPlus := poissonGraphMean_series_summable hV hE01 t C ht hC fp hfp0 hfpC
  have hPoissonMinus := poissonGraphMean_series_summable hV hE01 t C ht hC fn hfn0 hfnC
  have hGraphPlus := independentGraphMean_series_summable
    (looplessRate t) C fp hMass0 hTotal hfp0 hfpC
  have hGraphMinus := independentGraphMean_series_summable
    (looplessRate t) C fn hMass0 hTotal hfn0 hfnC
  have hMeanSub (m : ℕ) :
      uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)) =
        uniformMean (fun x : EdgeTuple V m => fp (tupleGraph x)) -
          uniformMean (fun x : EdgeTuple V m => fn (tupleGraph x)) := by
    let k : Bool → EdgeTuple V m → ℝ := fun b x =>
      if b then -fn (tupleGraph x) else fp (tupleGraph x)
    have hk (x : EdgeTuple V m) :
        (∑ b : Bool, k b x) = f (tupleGraph x) := by
      simp [k, hdecomp]
      ring
    have hlin :
        uniformMean (fun x : EdgeTuple V m => ∑ b : Bool, k b x) =
          ∑ b : Bool, uniformMean (k b) := hE08.2.2 (EdgeTuple V m) Bool k
    calc
      uniformMean (fun x : EdgeTuple V m => f (tupleGraph x)) =
          uniformMean (fun x : EdgeTuple V m => ∑ b : Bool, k b x) := by
            congr 1
            funext x
            exact (hk x).symm
      _ = ∑ b : Bool, uniformMean (k b) := hlin
      _ = uniformMean (fun x : EdgeTuple V m => fp (tupleGraph x)) -
          uniformMean (fun x : EdgeTuple V m => fn (tupleGraph x)) := by
            simp [k, uniformMean, Finset.sum_neg_distrib]
            ring
  have hPoissonDecomp :
      poissonGraphMean t f = poissonGraphMean t fp - poissonGraphMean t fn := by
    change (∑' m, poissonWeight t m *
        uniformMean (fun x : EdgeTuple V m => f (tupleGraph x))) = _
    calc
      _ = ∑' m, (poissonWeight t m *
          uniformMean (fun x : EdgeTuple V m => fp (tupleGraph x)) -
        poissonWeight t m * uniformMean (fun x : EdgeTuple V m => fn (tupleGraph x))) := by
          congr 1
          funext m
          rw [hMeanSub m]
          ring
      _ = poissonGraphMean t fp - poissonGraphMean t fn := by
          simpa [poissonGraphMean, poissonMixture] using hPoissonPlus.tsum_sub hPoissonMinus
  have hGraphDecomp :
      independentPoissonGraphMean (looplessRate t) f =
        independentPoissonGraphMean (looplessRate t) fp -
          independentPoissonGraphMean (looplessRate t) fn := by
    change (∑' G : MGraph V, independentPoissonGraphMass (looplessRate t) G * f G) = _
    calc
      _ = ∑' G : MGraph V,
          (independentPoissonGraphMass (looplessRate t) G * fp G -
            independentPoissonGraphMass (looplessRate t) G * fn G) := by
          congr 1
          funext G
          rw [hdecomp G]
          ring
      _ = independentPoissonGraphMean (looplessRate t) fp -
          independentPoissonGraphMean (looplessRate t) fn :=
            hGraphPlus.tsum_sub hGraphMinus
  have hPlus := poissonGraphMean_eq_countMean_nonneg hV hPreSplit hE01 t C ht fp hfp0 hfpC
  have hMinus := poissonGraphMean_eq_countMean_nonneg hV hPreSplit hE01 t C ht fn hfn0 hfnC
  calc
    poissonGraphMean t f = poissonGraphMean t fp - poissonGraphMean t fn := hPoissonDecomp
    _ = countMean (t / ((Fintype.card V).choose 2 : ℝ)) fp -
        countMean (t / ((Fintype.card V).choose 2 : ℝ)) fn := by rw [hPlus, hMinus]
    _ = countMean (t / ((Fintype.card V).choose 2 : ℝ)) f := by
      unfold countMean
      rw [← hRate]
      exact hGraphDecomp.symm

end ThLean.W.S547

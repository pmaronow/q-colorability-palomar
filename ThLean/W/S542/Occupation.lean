module

public import ThLean.BP.S5.Occupation

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S542
open ThLean.BP.S5
open ThresholdFoundations

private theorem pair_nonempty_fin (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (Pair (Fin n)) := by
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  refine ⟨⟨s(u, v), ?_⟩⟩
  intro w hw
  have heq := Sym2.eq_iff.mp hw
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst w
    exact huv (by simpa [eq_comm] using h2)
  · subst w
    exact huv (by simpa [eq_comm] using h2)

private theorem tupleGraph_loopless_fin (n m : ℕ) (x : EdgeTuple (Fin n) m) :
    Loopless (tupleGraph x) := by
  intro v
  unfold tupleGraph
  apply Finset.card_eq_zero.mpr
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using (x i).property v

private abbrev poissonPairFintype (N : ℕ) : Fintype (Pair (Fin N)) := by
  letI : DecidableEq (Fin N) := fun a b => Classical.propDecidable _
  exact @Subtype.fintype (Sym2 (Fin N)) (fun e => ∀ v : Fin N, e ≠ s(v, v))
    (fun _ => Fintype.decidableForallFintype) Sym2.instFintype

private abbrev poissonTupleFintype (N m : ℕ) : Fintype (EdgeTuple (Fin N) m) :=
  @Pi.instFintype (Fin m) (fun _ => Pair (Fin N)) (instDecidableEqFin m)
    (Fin.fintype m) (fun _ => poissonPairFintype N)

private theorem nmTime_poissonMixture
    (hpre : ThresholdFoundations.PreFiniteLawsStatement.{0, 0})
    (q N D : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    nmTime q N D t = poissonMixture t
      (fun m => uniformMean (fun x : EdgeTuple (Fin N) m =>
        nmProbability q D (tupleGraph x))) := by
  haveI : Nonempty (Pair (Fin N)) := pair_nonempty_fin N hN
  have htup (m : ℕ) : Nonempty (EdgeTuple (Fin N) m) :=
    ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair (Fin N)))⟩
  have hcore := hpre.1
  have havg (m : ℕ) :
      @uniformMean (EdgeTuple (Fin N) m) (poissonTupleFintype N m)
        (fun x => nmProbability q D (tupleGraph x)) =
      uniformMean (fun x : EdgeTuple (Fin N) m => nmProbability q D (tupleGraph x)) := by
    letI : Nonempty (EdgeTuple (Fin N) m) := htup m
    simpa using (@hcore (EdgeTuple (Fin N) m) (EdgeTuple (Fin N) m)
      (poissonTupleFintype N m) (inferInstance : Fintype (EdgeTuple (Fin N) m))
      (htup m) (htup m) (Equiv.refl _) (fun x => nmProbability q D (tupleGraph x)))
  unfold nmTime poissonGraphMean poissonMixture
  apply tsum_congr
  intro m
  simpa only [Function.comp_apply] using
    congrArg (fun z : ℝ => poissonWeight t m * z) (havg m)

private theorem uniformProb_nonneg_local {α : Type} [Fintype α] (P : α → Prop) :
    0 ≤ uniformProb P := by
  unfold uniformProb uniformMean
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro x hx
    unfold indicator
    split_ifs <;> norm_num
  · positivity

private theorem uniformMean_mono_local {α : Type} [Fintype α] [Nonempty α]
    (f g : α → ℝ) (h : ∀ x, f x ≤ g x) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun x _ => h x
  · positivity

theorem S5_33AStatement_of_deps
    (h10 : S5_10Statement)
    (h17 : S5_17BStatement)
    (h05 : S5_05Statement)
    (h27 : S5_27Statement)
    (h28a : S5_28AStatement)
    (h28b : S5_28BStatement)
    (h29a : S5_29AStatement)
    (hpre : ThresholdFoundations.PreFiniteLawsStatement.{0, 0}) :
    S5_33AStatement := by
  intro q n D hq hn hD hDn
  let N : ℕ := n - 1
  have hN2 : 2 ≤ N := by dsimp [N]; omega
  have hD_N : D ≤ N := by dsimp [N]; omega
  have hadvance := h17 q N D hq (by dsimp [N]; omega) hD hD_N
  have hfinite : identificationAdvance (V := Fin N) q D < ∞ := hadvance.2.1

  have h28 : S5_28Statement := S5_28_assembly h28a h28b
  have h29 : S5_29Statement := S5_29_assembly h05 h27 h28 h29a
  haveI : Nonempty (Pair (Fin N)) := pair_nonempty_fin N hN2
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩

  let a : ℕ → ℝ := fun m => uniformMean (fun x : EdgeTuple (Fin N) m =>
    nmProbability q D (tupleGraph x))
  let b : ℕ → ℝ := fun m => uniformMean (fun x : EdgeTuple (Fin N) m =>
    identificationFailureProbability q D (tupleGraph x))

  have hpoint : ∀ m, a m ≤ b m := by
    intro m
    letI : Nonempty (EdgeTuple (Fin N) m) :=
      ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair (Fin N)))⟩
    apply uniformMean_mono_local
    intro x
    have hcardD : D ≤ Fintype.card (Fin N) := by simpa using hD_N
    exact h29 (V := Fin N) q D hq hD hcardD
      (tupleGraph x) (tupleGraph_loopless_fin N m x)

  have hnonneg : ∀ m, 0 ≤ a m := by
    intro m
    letI : Nonempty (EdgeTuple (Fin N) m) :=
      ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair (Fin N)))⟩
    have h := uniformMean_mono_local (fun _ : EdgeTuple (Fin N) m => 0)
      (fun x => nmProbability q D (tupleGraph x)) (fun x => uniformProb_nonneg_local _)
    change 0 ≤ uniformMean (fun x : EdgeTuple (Fin N) m => nmProbability q D (tupleGraph x))
    simpa [uniformMean] using h

  have hsumB : HasSum b (advanceReal q N D) := by
    simpa [b] using hadvance.2.2.2.2
  have hsumA : Summable a := by
    apply Summable.of_nonneg_of_le hnonneg hpoint
    exact hsumB.summable
  have htsum : (∑' m, a m) ≤ advanceReal q N D := by
    exact hasSum_le hpoint hsumA.hasSum hsumB

  have hnRpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnNat : 2 < n := by dsimp [N] at hN2; omega
  have hn2R : (2 : ℝ) < n := Nat.cast_lt.mpr hnNat
  have hp : 0 < (((n : ℝ) - 2) / n) := div_pos (by linarith) hnRpos
  let p : ℝ := ((n : ℝ) - 2) / n
  have hocc := (h10 p hp).2 a hnonneg hsumA
  have hNMmix (t : ℝ) : nmTime q N D t = poissonMixture t a := by
    simpa only [a] using nmTime_poissonMixture hpre q N D hN2 t
  have hint : IntegrableOn
      (fun t => nmTime q N D (p * t)) (Set.Ici 0) := by
    simpa only [hNMmix] using hocc.1
  have hcoef : 1 / p = (n : ℝ) / ((n : ℝ) - 2) := by
    dsimp [p]
    have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnRpos
    have hdenR : (n : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hnR, hdenR]
  have hinter :
      (∫ t in Set.Ici (0 : ℝ), nmTime q N D (p * t)) =
        ((n : ℝ) / ((n : ℝ) - 2)) * ∑' m, a m := by
    calc
      _ = (1 / p) * ∑' m, a m := by
        simpa only [hNMmix] using hocc.2
      _ = ((n : ℝ) / ((n : ℝ) - 2)) * ∑' m, a m := by rw [hcoef]
  have hbound :
      (∫ t in Set.Ici (0 : ℝ), nmTime q N D (p * t)) ≤
        ((n : ℝ) / ((n : ℝ) - 2)) * advanceReal q N D := by
    rw [hinter]
    apply mul_le_mul_of_nonneg_left htsum
    positivity

  refine ⟨hfinite, ?_, ?_, ?_, ?_⟩
  · simpa [a, N] using hsumA
  · simpa only [N, p] using hint
  · simpa only [N, p, a] using hinter
  · simpa only [N, p] using hbound

end ThLean.W.S542

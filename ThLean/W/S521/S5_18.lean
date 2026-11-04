module

public import ThLean.W.S521.PairCounting

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S521
open ThresholdFoundations
open ThLean.BP.S5
universe u v

private def edgeMono {V : Type*} {q : ℕ} (σ : V → Fin q) (e : Pair V) : Prop :=
  ∃ u v, e.val = s(u, v) ∧ σ u = σ v

private lemma isColoring_tuple_iff {V : Type*} [Fintype V] {q m : ℕ}
    (σ : V → Fin q) (x : EdgeTuple V m) :
    IsColoring q (tupleGraph x) σ ↔ ∀ i, ¬ edgeMono σ (x i) := by
  constructor
  · intro hc i hmono
    rcases hmono with ⟨u, v, hev, hcolor⟩
    have hi : i ∈ Finset.univ.filter (fun j : Fin m => (x j).val = s(u, v)) := by
      simp [hev]
    have hcount : 0 < tupleGraph x (s(u, v)) := by
      rw [tupleGraph]
      exact Finset.card_pos.mpr ⟨i, hi⟩
    exact (hc u v hcount) hcolor
  · intro hgood u v hcount
    have hcard : 0 < (Finset.univ.filter (fun i : Fin m => (x i).val = s(u, v))).card := by
      simpa [tupleGraph] using hcount
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
    have hev : (x i).val = s(u, v) := (Finset.mem_filter.mp hi).2
    have hcolors : σ u ≠ σ v := by
      intro hEq
      exact hgood i ⟨u, v, hev, hEq⟩
    exact hcolors

private lemma fixedColorTupleProb_eq_pow {V : Type u} [Fintype V] {q : ℕ}
    (hfinite : ThresholdFoundations.PreFiniteLawsStatement.{u, u})
    (hne : Nonempty (Pair V)) (σ : V → Fin q) :
    ∀ m : ℕ, uniformProb (fun x : EdgeTuple V m => ∀ i, ¬ edgeMono σ (x i)) =
      (uniformProb (fun e : Pair V => ¬ edgeMono σ e))^m := by
  intro m
  induction m with
  | zero => simp [uniformProb, uniformMean, indicator]
  | succ m ih =>
    rcases hfinite with ⟨hreindex, hfub, hrest⟩
    have hfinite' : ThresholdFoundations.PreFiniteLawsStatement.{u, u} :=
      ⟨hreindex, hfub, hrest⟩
    let e : Pair V × (Fin m → Pair V) ≃ (Fin (m + 1) → Pair V) :=
      Fin.consEquiv (fun _ : Fin (m + 1) => Pair V)
    have hre := hreindex (Pair V × (Fin m → Pair V)) (Fin (m + 1) → Pair V) e
      (fun x => indicator (∀ i, ¬ edgeMono σ (x i)))
    have hforall (z : Pair V × (Fin m → Pair V)) :
        (∀ i : Fin (m + 1), ¬ edgeMono σ (e z i)) ↔
          (¬ edgeMono σ z.1 ∧ ∀ i : Fin m, ¬ edgeMono σ (z.2 i)) := by
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [e, Fin.consEquiv] using h 0
        · intro i
          simpa [e, Fin.consEquiv] using h i.succ
      · rintro ⟨h0, ht⟩ i
        refine Fin.cases ?_ ?_ i
        · simpa [e, Fin.consEquiv] using h0
        · intro j
          simpa [e, Fin.consEquiv] using ht j
    have hsplit : uniformProb (fun x : Fin (m + 1) → Pair V =>
        ∀ i, ¬ edgeMono σ (x i)) =
        uniformProb (fun z : Pair V × (Fin m → Pair V) =>
          ¬ edgeMono σ z.1 ∧ ∀ i, ¬ edgeMono σ (z.2 i)) := by
      calc
        _ = uniformMean (fun z : Pair V × (Fin m → Pair V) =>
            indicator (∀ i, ¬ edgeMono σ (e z i))) := by
          unfold uniformProb
          exact hre.symm
        _ = _ := by
          unfold uniformProb
          congr 1
          funext z
          exact congrArg indicator (propext (hforall z))
    letI : Nonempty (Pair V) := hne
    letI : Nonempty (Fin m → Pair V) := ⟨fun _ => Classical.choice hne⟩
    rw [hsplit, uniformProb_prod (A := Pair V) (B := Fin m → Pair V)
      (hfinite := hfinite') (P := fun e => ¬ edgeMono σ e)
      (Q := fun x => ∀ i, ¬ edgeMono σ (x i))]
    rw [ih]
    ring

theorem S5_18Statement_of_deps
    (hfinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0}) :
    ThLean.BP.S5.S5_18Statement := by
  intro V _ q hq hN
  constructor
  · intro σ
    exact monochromatic_pair_fraction q hq hN σ
  · intro m
    classical
    have h2n : 2 ≤ Fintype.card V := by omega
    have hpairCard : 0 < Fintype.card (Pair V) := by
      rw [pair_card]
      exact Nat.choose_pos h2n
    letI : Nonempty (Pair V) := Fintype.card_pos_iff.mp hpairCard
    letI : Nonempty (EdgeTuple V m) :=
      ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair V))⟩
    let b : ℝ := 1 - 1 / (2 * (q : ℝ))
    have hmono (σ : V → Fin q) :
        1 / (2 * (q : ℝ)) ≤ uniformProb (fun e : Pair V => edgeMono σ e) := by
      simpa [edgeMono] using monochromatic_pair_fraction q hq hN σ
    have hgood (σ : V → Fin q) :
        uniformProb (fun e : Pair V => ¬ edgeMono σ e) ≤ b := by
      rw [uniformProb_compl]
      dsimp [b]
      linarith [hmono σ]
    have hfixed (σ : V → Fin q) :
        uniformProb (fun x : EdgeTuple V m => ∀ i, ¬ edgeMono σ (x i)) ≤ b^m := by
      calc
        _ = (uniformProb (fun e : Pair V => ¬ edgeMono σ e))^m :=
          fixedColorTupleProb_eq_pow hfinite (inferInstance : Nonempty (Pair V)) σ m
        _ ≤ b^m := pow_le_pow_left₀ (uniformProb_nonneg _) (hgood σ) m
    have hcolor (x : EdgeTuple V m) :
        Colorable q (tupleGraph x) ↔ ∃ σ : V → Fin q, ∀ i, ¬ edgeMono σ (x i) := by
      simp [Colorable, isColoring_tuple_iff]
    have hsurv : processSurvival (V := V) q m =
        uniformProb (fun x : EdgeTuple V m => ∃ σ : V → Fin q, ∀ i, ¬ edgeMono σ (x i)) := by
      have hbase : processSurvival (V := V) q m =
          uniformProb (fun x : EdgeTuple V m => Colorable q (tupleGraph x)) := by
        simp [processSurvival, survival]
      rw [hbase]
      congr 1
      funext x
      exact propext (hcolor x)
    calc
      processSurvival (V := V) q m =
          uniformProb (fun x : EdgeTuple V m => ∃ σ : V → Fin q, ∀ i, ¬ edgeMono σ (x i)) := hsurv
      _ ≤ ∑ σ : V → Fin q,
          uniformProb (fun x : EdgeTuple V m => ∀ i, ¬ edgeMono σ (x i)) :=
        uniformProb_exists_le (A := EdgeTuple V m) (B := V → Fin q)
          (fun σ (x : EdgeTuple V m) => ∀ i : Fin m, ¬ edgeMono σ (x i))
      _ ≤ ∑ _σ : V → Fin q, b^m := Finset.sum_le_sum fun σ _ => hfixed σ
      _ = (q : ℝ)^(Fintype.card V) * b^m := by
        simp [b, Finset.sum_const, nsmul_eq_mul]

end ThLean.W.S521

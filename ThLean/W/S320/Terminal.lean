module

public import ThLean.BP.S3.Terminal

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S320
open ThresholdFoundations

private theorem pair_card_pos {V : Type u} [Fintype V]
    (hV : 2 ≤ Fintype.card V) : 0 < Fintype.card (Pair V) := by
  apply Fintype.card_pos_iff.mpr
  have hv : 1 < Fintype.card V := by omega
  obtain ⟨v₁⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨v₂, hv₂⟩ := Fintype.exists_ne_of_one_lt_card hv v₁
  refine ⟨⟨s(v₁, v₂), ?_⟩⟩
  intro w hw
  have hEq : s(v₁, v₂) = s(w, w) := hw
  rcases Sym2.eq_iff.mp hEq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hv₂ (h₂.trans h₁.symm)
  · exact hv₂ (h₂.trans h₁.symm)

private theorem tupleGraph_snoc {V : Type u} [Fintype V] {m : ℕ}
    (x : EdgeTuple V (m + 1)) :
    tupleGraph x = addPair (tupleGraph (ThLean.BP.S3.initTuple x))
      (ThLean.BP.S3.lastPair x) := by
  classical
  funext e
  change (Finset.univ.filter (fun i : Fin (m + 1) => (x i).val = e)).card =
    Function.update (tupleGraph (ThLean.BP.S3.initTuple x))
      (ThLean.BP.S3.lastPair x).val
      (tupleGraph (ThLean.BP.S3.initTuple x) (ThLean.BP.S3.lastPair x).val + 1) e
  have hcount :
      (Finset.univ.filter (fun i : Fin (m + 1) => (x i).val = e)).card =
        (Finset.univ.filter
          (fun i : Fin m => (ThLean.BP.S3.initTuple x i).val = e)).card +
          (if (ThLean.BP.S3.lastPair x).val = e then 1 else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fin.sum_univ_castSucc]
    simp only [ThLean.BP.S3.initTuple, ThLean.BP.S3.lastPair,
      Fin.val_castSucc, Fin.val_last]
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    rfl
  rw [hcount]
  by_cases he : e = (ThLean.BP.S3.lastPair x).val
  · subst e
    have hbase :
        (Finset.univ.filter
          (fun i : Fin m => (ThLean.BP.S3.initTuple x i).val =
            (ThLean.BP.S3.lastPair x).val)).card =
          tupleGraph (ThLean.BP.S3.initTuple x) (ThLean.BP.S3.lastPair x).val := rfl
    calc
      _ = (Finset.univ.filter
          (fun i : Fin m => (ThLean.BP.S3.initTuple x i).val =
            (ThLean.BP.S3.lastPair x).val)).card + 1 := by simp
      _ = tupleGraph (ThLean.BP.S3.initTuple x) (ThLean.BP.S3.lastPair x).val + 1 := by
        rw [hbase]
      _ = Function.update (tupleGraph (ThLean.BP.S3.initTuple x))
          (ThLean.BP.S3.lastPair x).val
          (tupleGraph (ThLean.BP.S3.initTuple x) (ThLean.BP.S3.lastPair x).val + 1)
          (ThLean.BP.S3.lastPair x).val := by simp
  · have he' : ¬ (ThLean.BP.S3.lastPair x).val = e := by
      intro h
      exact he h.symm
    have hbase :
        (Finset.univ.filter
          (fun i : Fin m => (ThLean.BP.S3.initTuple x i).val = e)).card =
          tupleGraph (ThLean.BP.S3.initTuple x) e := rfl
    calc
      _ = (Finset.univ.filter
          (fun i : Fin m => (ThLean.BP.S3.initTuple x i).val = e)).card := by
            simpa [he'] using hcount
      _ = tupleGraph (ThLean.BP.S3.initTuple x) e := hbase
      _ = Function.update (tupleGraph (ThLean.BP.S3.initTuple x))
          (ThLean.BP.S3.lastPair x).val
          (tupleGraph (ThLean.BP.S3.initTuple x) (ThLean.BP.S3.lastPair x).val + 1) e := by
            simp [Function.update, he]

private theorem uniformMeanENN_if_const {E : Type u} [Fintype E]
    (P : E → Prop) [DecidablePred P] (c : ℝ≥0∞)
    (hE : 0 < Fintype.card E) :
    uniformMeanENN (fun e => if P e then c else 0) =
      ENNReal.ofReal (uniformProb P) * c := by
  have hER : (0 : ℝ) < Fintype.card E := by exact_mod_cast hE
  have hsum :
      (∑ e, (if P e then c else 0)) =
        (∑ e, (if P e then (1 : ℝ≥0∞) else 0)) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hp : P e <;> simp [hp]
  have hcountR :
      (∑ e, (if P e then (1 : ℝ) else 0)) =
        ((Finset.univ.filter P).card : ℝ) := by
    simpa using (Finset.sum_boole P Finset.univ :
      (∑ e ∈ Finset.univ, (if P e then (1 : ℝ) else 0)) = _)
  have hnum :
      (∑ e, (if P e then (1 : ℝ) else 0)) =
        (∑ e, indicator (P e)) := by
    apply Finset.sum_congr rfl
    intro e he
    by_cases hp : P e <;> simp [indicator, hp]
  have hcountE :
      (∑ e, (if P e then (1 : ℝ≥0∞) else 0)) =
        ((Finset.univ.filter P).card : ℝ≥0∞) := by
    simpa using (Finset.sum_boole P Finset.univ :
      (∑ e ∈ Finset.univ, (if P e then (1 : ℝ≥0∞) else 0)) = _)
  have hprob : uniformProb P =
      ((Finset.univ.filter P).card : ℝ) / Fintype.card E := by
    unfold uniformProb uniformMean
    rw [← hnum, hcountR]
  have hscalar :
      (∑ e, (if P e then (1 : ℝ≥0∞) else 0)) /
          (Fintype.card E : ℝ≥0∞) = ENNReal.ofReal (uniformProb P) := by
    rw [hcountE, hprob, ENNReal.ofReal_div_of_pos hER]
    simp [ENNReal.ofReal_natCast]
  unfold uniformMeanENN
  rw [hsum]
  calc
    ((∑ e, (if P e then (1 : ℝ≥0∞) else 0)) * c) /
        (Fintype.card E : ℝ≥0∞) =
      ((∑ e, (if P e then (1 : ℝ≥0∞) else 0)) /
        (Fintype.card E : ℝ≥0∞)) * c := by
          simp only [div_eq_mul_inv]
          ac_rfl
    _ = ENNReal.ofReal (uniformProb P) * c := by rw [hscalar]

private theorem terminalEdgeMean_eq_kappaKind {V : Type u} [Fintype V]
    (q : ℕ) (A : MGraph V → Pair V → Prop) (G : MGraph V)
    (hG : MGraph V → ℝ≥0∞) (hV : 2 ≤ Fintype.card V) :
    uniformMeanENN (fun e : Pair V =>
      if FrozenPair q G e ∧ A G e then hG G else 0) =
      ENNReal.ofReal (kappaKind q A G) * hG G := by
  change uniformMeanENN (fun e : Pair V =>
      if FrozenPair q G e ∧ A G e then hG G else 0) =
    ENNReal.ofReal (uniformProb (fun e : Pair V => FrozenPair q G e ∧ A G e)) * hG G
  letI : DecidablePred (fun e : Pair V => FrozenPair q G e ∧ A G e) :=
    fun e => instDecidableAnd
  exact uniformMeanENN_if_const
    (P := fun e : Pair V => FrozenPair q G e ∧ A G e)
    (c := hG G) (pair_card_pos hV)

theorem S3_17Statement_of_deps
    (h4a : ThLean.BP.S3.S3_04aStatement.{u})
    (h4b : ThLean.BP.S3.S3_04bStatement.{u})
    (h10 : ThLean.BP.S3.S3_10Statement.{u}) :
    ThLean.BP.S3.S3_17Statement.{u} := by
  intro V instV q hq hV A
  constructor
  · intro m h
    have hbad (G : MGraph V) (e : Pair V) :
        (Colorable q G ∧ ¬ Colorable q (addPair G e)) ↔ FrozenPair q G e := by
      constructor
      · rintro ⟨hc, hfail⟩
        by_contra hnot
        apply hfail
        exact ((h10 V q hq hV).1 G e).mpr ⟨hc, hnot⟩
      · intro hfr
        rcases hfr with ⟨u, v, hev, hF⟩
        refine ⟨hF.1, ?_⟩
        intro hadd
        exact (((h10 V q hq hV).1 G e).mp hadd).2 ⟨u, v, hev, hF⟩
    have hinner (x : EdgeTuple V m) :
        uniformMeanENN (fun e : Pair V =>
          if Colorable q (tupleGraph x) ∧
            ¬ Colorable q (addPair (tupleGraph x) e) then
              if A (tupleGraph x) e then h (tupleGraph x) else 0 else 0) =
        ENNReal.ofReal (kappaKind q A (tupleGraph x)) * h (tupleGraph x) := by
      have hfun :
          (fun e : Pair V =>
            if Colorable q (tupleGraph x) ∧
              ¬ Colorable q (addPair (tupleGraph x) e) then
                if A (tupleGraph x) e then h (tupleGraph x) else 0 else 0) =
          (fun e : Pair V =>
            if FrozenPair q (tupleGraph x) e ∧ A (tupleGraph x) e then
              h (tupleGraph x) else 0) := by
        funext e
        by_cases hb : Colorable q (tupleGraph x) ∧
            ¬ Colorable q (addPair (tupleGraph x) e)
        · have hfr := (hbad (tupleGraph x) e).mp hb
          by_cases ha : A (tupleGraph x) e <;> simp [hb, hfr, ha]
        · have hfr : ¬ FrozenPair q (tupleGraph x) e := by
            intro hf
            exact hb ((hbad (tupleGraph x) e).mpr hf)
          simp [hb, hfr]
      rw [hfun]
      exact terminalEdgeMean_eq_kappaKind q A (tupleGraph x) h hV
    unfold terminalStepENN graphMeanENN
    congr 1
    funext x
    rw [hinner x]
  · intro hA ω m
    have hproc : processGraph ω (m + 1) =
        addPair (processGraph ω m) (ω m) := by
      let x : EdgeTuple V (m + 1) := fun i => ω i.val
      have hinit : ThLean.BP.S3.initTuple x =
          (fun i : Fin m => ω i.val) := by
        funext i
        rfl
      have hlast : ThLean.BP.S3.lastPair x = ω m := by
        apply Subtype.ext
        rfl
      change tupleGraph x =
        addPair (tupleGraph (fun i : Fin m => ω i.val)) (ω m)
      rw [tupleGraph_snoc x, hinit, hlast]
    rcases h4a V q hq with ⟨_, hchar, _, _⟩
    constructor
    · intro hkind
      have hfr := hA (processGraph ω m) (ω m) hkind
      rcases hfr with ⟨u, v, hev, hF⟩
      have hcol : Colorable q (processGraph ω m) := hF.1
      have hfail : ¬ Colorable q (processGraph ω (m + 1)) := by
        rw [hproc]
        intro hadd
        exact (((h10 V q hq hV).1 (processGraph ω m) (ω m)).mp hadd).2
          ⟨u, v, hev, hF⟩
      have htime : hittingTime q ω = ((m + 1 : ℕ) : WithTop ℕ) :=
        (hchar ω m).2.mpr ⟨hcol, hfail⟩
      have hterminal := h4b V q hq ω (m + 1) htime
      refine ⟨htime, ?_⟩
      refine ⟨processGraph ω m, ?_⟩
      refine ⟨ω m, ?_⟩
      refine ⟨?_, ?_, hkind⟩
      · simpa using hterminal.2.1
      · simpa using hterminal.2.2.1
    · rintro ⟨htime, G, e, hlast, hfinal, hkind⟩
      have hterminal := h4b V q hq ω (m + 1) htime
      have hlast' : lastGraph q ω = some (processGraph ω m) := by
        simpa using hterminal.2.1
      have hfinal' : finalEdge q ω = some (ω m) := by
        simpa using hterminal.2.2.1
      have hG : G = processGraph ω m := Option.some.inj (hlast.symm.trans hlast')
      have he : e = ω m := Option.some.inj (hfinal.symm.trans hfinal')
      subst G
      subst e
      exact hkind

end ThLean.W.S320

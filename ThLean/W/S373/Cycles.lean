import ThLean.BP.S3.Cycles

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.W.S373
open ThresholdFoundations

private lemma uniformProb_eq_filter_card {Ω : Type u} [Fintype Ω]
    (P : Ω → Prop) :
    uniformProb P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  simp [uniformProb, uniformMean, indicator]

private lemma uniformProb_iUnion_le {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (hΩ : 0 < Fintype.card Ω) (P : ι → Ω → Prop) :
    uniformProb (fun ω => ∃ i, P i ω) ≤ ∑ i, uniformProb (P i) := by
  classical
  unfold uniformProb uniformMean
  rw [← Finset.sum_div, Finset.sum_comm]
  apply (div_le_div_iff_of_pos_right (by exact_mod_cast hΩ)).2
  apply Finset.sum_le_sum
  intro ω hω
  by_cases h : ∃ j, P j ω
  · rcases h with ⟨j, hj⟩
    have hex : ∃ i : ι, P i ω := ⟨j, hj⟩
    calc
      indicator (∃ i, P i ω) = 1 := by simp [indicator, hex]
      _ ≤ ∑ i, indicator (P i ω) := by
        have hs : indicator (P j ω) ≤ ∑ i, indicator (P i ω) := by
          have hnonneg : ∀ i ∈ (Finset.univ : Finset ι),
              0 ≤ indicator (P i ω) := by
            intro i hi
            by_cases hp : P i ω <;> simp [indicator, hp]
          simpa using Finset.single_le_sum hnonneg
            (Finset.mem_univ j)
        simpa [indicator, hj] using hs
  · have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ indicator (P i ω) := by
      intro i hi
      by_cases hp : P i ω <;> simp [indicator, hp]
    simp [indicator, h]

private lemma list_length_eq_card_toFinset {α : Type u} [DecidableEq α]
    (l : List α) (hl : l.Nodup) : l.length = l.toFinset.card := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hn := List.nodup_cons.mp hl
    simp [List.toFinset_cons, hn.1, ih hn.2]

private lemma list_countP_ofFn {α : Type u} {n : ℕ}
    (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).countP p = (Finset.univ.filter (fun i => p (f i))).card := by
  classical
  rw [List.countP_eq_length_filter, List.ofFn_eq_map,
    List.filter_map]
  simp only [List.length_map]
  rw [list_length_eq_card_toFinset _ ((List.nodup_finRange n).filter _)]
  simp [List.toFinset_filter, List.toFinset_finRange]

private def occurrencePair {V : Type u} [Fintype V]
    (F : MGraph V) (hF : Loopless F) (o : Occurrence F) : Pair V :=
  ⟨o.1, by
    intro v hev
    have hp : 0 < F o.1 := by have := o.2.isLt; omega
    rw [hev, hF v] at hp
    exact Nat.lt_irrefl 0 hp⟩

private def occurrencePairFn {V : Type u} [Fintype V]
    (F : MGraph V) (hF : Loopless F) :
    Fin (Fintype.card (Occurrence F)) → Pair V :=
  fun i => occurrencePair F hF ((Fintype.equivFin (Occurrence F)).symm i)

private def occurrencePairList {V : Type u} [Fintype V]
    (F : MGraph V) (hF : Loopless F) : List (Pair V) :=
  List.ofFn (occurrencePairFn F hF)

private lemma occurrencePairFiber_card {V : Type u} [Fintype V]
    (F : MGraph V) (hF : Loopless F) (e : Pair V) :
    Fintype.card {o : Occurrence F // occurrencePair F hF o = e} = F e.val := by
  classical
  let E₁ : {o : Occurrence F // occurrencePair F hF o = e} ≃
      {o : Occurrence F // o.1 = e.val} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro o
      constructor
      · intro ho
        exact congrArg Subtype.val ho
      · intro ho
        exact Subtype.ext ho)
  let E₂ : {o : Occurrence F // o.1 = e.val} ≃ Fin (F e.val) := {
    toFun := fun o => Fin.cast (congrArg F o.property) o.val.2
    invFun := fun i => (⟨⟨e.val, i⟩, rfl⟩ : {o : Occurrence F // o.1 = e.val})
    left_inv := fun o => by
      rcases o with ⟨⟨a, i⟩, ha⟩
      change a = e.val at ha
      subst a
      rfl
    right_inv := fun i => by simp
  }
  calc
    _ = Fintype.card {o : Occurrence F // o.1 = e.val} := Fintype.card_congr E₁
    _ = Fintype.card (Fin (F e.val)) := Fintype.card_congr E₂
    _ = F e.val := Fintype.card_fin _

private lemma occurrencePairList_count {V : Type u} [Fintype V]
    (F : MGraph V) (hF : Loopless F) (e : Pair V) :
    (occurrencePairList F hF).count e = F e.val := by
  classical
  change (List.ofFn (occurrencePairFn F hF)).count e = F e.val
  calc
    (List.ofFn (occurrencePairFn F hF)).count e =
        (Finset.univ.filter (fun i : Fin (Fintype.card (Occurrence F)) =>
          occurrencePairFn F hF i == e)).card := by
      rw [List.count_eq_countP]
      exact list_countP_ofFn (occurrencePairFn F hF) (fun a => a == e)
    _ = Fintype.card {i : Fin (Fintype.card (Occurrence F)) //
        occurrencePair F hF ((Fintype.equivFin (Occurrence F)).symm i) = e} := by
      let s := Finset.univ.filter (fun i : Fin (Fintype.card (Occurrence F)) =>
        occurrencePairFn F hF i == e)
      let E₁ : {i : Fin (Fintype.card (Occurrence F)) // i ∈ s} ≃
          {i : Fin (Fintype.card (Occurrence F)) //
            (occurrencePairFn F hF i == e) = true} :=
        Equiv.subtypeEquiv (Equiv.refl _) (by
          intro i
          simp [s])
      let E₂ : {i : Fin (Fintype.card (Occurrence F)) //
          (occurrencePairFn F hF i == e) = true} ≃
          {i : Fin (Fintype.card (Occurrence F)) //
            occurrencePair F hF ((Fintype.equivFin (Occurrence F)).symm i) = e} :=
        Equiv.subtypeEquiv (Equiv.refl _) (by
          intro i
          constructor
          · intro hi
            have heq : occurrencePairFn F hF i = e := beq_iff_eq.mp hi
            simpa [occurrencePairFn] using heq
          · intro hi
            have heq : occurrencePairFn F hF i = e := by
              simpa [occurrencePairFn] using hi
            exact beq_iff_eq.mpr heq)
      let E := E₁.trans E₂
      calc
        _ = s.card := by rfl
        _ = Fintype.card {i : Fin (Fintype.card (Occurrence F)) // i ∈ s} :=
          (Fintype.card_coe s).symm
        _ = Fintype.card {i : Fin (Fintype.card (Occurrence F)) //
            occurrencePair F hF ((Fintype.equivFin (Occurrence F)).symm i) = e} :=
          Fintype.card_congr E
    _ = Fintype.card {o : Occurrence F // occurrencePair F hF o = e} := by
      exact Fintype.card_congr <| Equiv.subtypeEquiv
        (Fintype.equivFin (Occurrence F)).symm (by intro i; rfl)
    _ = F e.val := occurrencePairFiber_card F hF e

private lemma card_occurrence_eq_edgeCount {V : Type u} [Fintype V]
    (F : MGraph V) : Fintype.card (Occurrence F) = edgeCount F := by
  simp [Occurrence, edgeCount]

private lemma tupleList_count {V : Type u} [Fintype V] {m : ℕ}
    (x : EdgeTuple V m) (e : Pair V) :
    (List.ofFn x).count e = tupleGraph x e.val := by
  classical
  rw [List.count_eq_countP]
  rw [list_countP_ofFn x (fun a => a == e)]
  simp [tupleGraph, beq_iff_eq]

private lemma list_count_eq_decide_count {α : Type u} [BEq α] [LawfulBEq α]
    [DecidableEq α] (l : List α) (a : α) :
    l.count a = l.countP (fun x => decide (x = a)) := by
  rw [List.count_eq_countP]
  congr 1
  funext x
  by_cases h : x = a <;> simp [h]

private lemma subgraph_iff_pair_bounds {V : Type u} [Fintype V]
    (F : MGraph V) (hF : Loopless F) {m : ℕ} (x : EdgeTuple V m) :
    subgraph F (tupleGraph x) ↔ ∀ e : Pair V, F e.val ≤ tupleGraph x e.val := by
  constructor
  · intro h e
    exact h e.val
  · intro h e
    by_cases he : ∃ v, e = s(v, v)
    · rcases he with ⟨v, rfl⟩
      simp [hF v]
    · let pe : Pair V := ⟨e, by
        intro v hev
        exact he ⟨v, hev⟩⟩
      exact h pe

private lemma card_fin_embedding_le (k m : ℕ) :
    Fintype.card (Fin k ↪ Fin m) ≤ m ^ k := by
  let emb : (Fin k ↪ Fin m) ↪ (Fin k → Fin m) :=
    ⟨fun f => f, fun f g h => by
      apply DFunLike.coe_injective
      exact h⟩
  calc
    Fintype.card (Fin k ↪ Fin m) ≤ Fintype.card (Fin k → Fin m) :=
      Fintype.card_le_of_embedding emb
    _ = m ^ k := by simp

theorem S3_70Statement_of_deps (h02 : ThLean.BP.S3.S3_02Statement.{u})
    (h69 : ThLean.BP.S3.S3_69Statement.{u}) :
    ThLean.BP.S3.S3_70Statement.{u} := by
  intro V instV hV F m hF
  classical
  let hPair : Nonempty (Pair V) := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
    exact ⟨⟨s(a, b), by
      intro c h
      have hab' := (Sym2.eq_iff.mp h)
      rcases hab' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hab (ha.trans hb.symm)
      · exact hab (ha.trans hb.symm)⟩⟩
  letI : Nonempty (Pair V) := hPair
  let Ω : Type u := EdgeTuple V m
  letI : Nonempty Ω := ⟨fun _ => Classical.choice hPair⟩
  let k : ℕ := Fintype.card (Occurrence F)
  let f : Fin k → Pair V := occurrencePairFn F hF
  let p : List (Pair V) := occurrencePairList F hF
  have hk : k = edgeCount F := by
    exact card_occurrence_eq_edgeCount F
  have hΩ : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr inferInstance
  have hprobEvent (x : EdgeTuple V m) :
      subgraph F (tupleGraph x) ↔ ∃ ι : Fin k ↪ Fin m, ∀ j, x (ι j) = f j := by
    have h69iff := (h69 (Pair V) p (List.ofFn x)).1
    have hcountIff :
        subgraph F (tupleGraph x) ↔
          ∀ e : Pair V, p.count e ≤ (List.ofFn x).count e := by
      constructor
      · intro hs e
        rw [occurrencePairList_count, tupleList_count]
        exact (subgraph_iff_pair_bounds F hF x).1 hs e
      · intro hc
        apply (subgraph_iff_pair_bounds F hF x).2
        intro e
        have he := hc e
        rw [occurrencePairList_count, tupleList_count] at he
        exact he
    let canonicalCount := fun (l : List (Pair V)) (e : Pair V) =>
      l.countP (fun a => decide (a = e))
    have hcountIff' :
        subgraph F (tupleGraph x) ↔
          ∀ e : Pair V, canonicalCount p e ≤ canonicalCount (List.ofFn x) e := by
      simpa only [canonicalCount, list_count_eq_decide_count] using hcountIff
    have h69iff' :
        (∀ e : Pair V, canonicalCount p e ≤ canonicalCount (List.ofFn x) e) ↔
          ∃ ι : Fin p.length ↪ Fin (List.ofFn x).length,
            ∀ j, p.get j = (List.ofFn x).get (ι j) := by
      simpa only [canonicalCount, list_count_eq_decide_count] using h69iff
    have hEmbedding := hcountIff'.trans h69iff'
    have hpLen : p.length = k := by simp [p, k, occurrencePairList]
    have hxLen : (List.ofFn x).length = m := List.length_ofFn
    have hpget (j : Fin p.length) : p.get j = f (Fin.cast hpLen j) := by
      simpa [p, f, occurrencePairList, occurrencePairFn, k, hpLen] using
        (List.get_ofFn (occurrencePairFn F hF) j)
    have hxget (i : Fin (List.ofFn x).length) :
        (List.ofFn x).get i = x (Fin.cast hxLen i) := by
      simpa [hxLen] using (List.get_ofFn x i)
    have hxcast (i : Fin m) : Fin.cast hxLen (Fin.cast hxLen.symm i) = i := by
      simp [Fin.cast_cast]
    have hEmbedding' :
        subgraph F (tupleGraph x) ↔
          ∃ ι : Fin k ↪ Fin m, ∀ j, f j = x (ι j) := by
      constructor
      · intro hs
        rcases hEmbedding.mp hs with ⟨ι, hi⟩
        let ι' : Fin k ↪ Fin m := {
          toFun := fun j => Fin.cast hxLen (ι (Fin.cast hpLen.symm j))
          inj' := by
            intro a b hab
            apply (Fin.cast_inj hpLen.symm).mp
            apply ι.injective
            exact (Fin.cast_inj hxLen).mp hab
        }
        refine ⟨ι', ?_⟩
        intro j
        let j' : Fin p.length := Fin.cast hpLen.symm j
        calc
          f j = p.get j' := by rw [hpget]; simp [j', Fin.cast_cast]
          _ = (List.ofFn x).get (ι j') := hi j'
          _ = x (ι' j) := by rw [hxget]; rfl
      · rintro ⟨ι, hi⟩
        let ι' : Fin p.length ↪ Fin (List.ofFn x).length := {
          toFun := fun j => Fin.cast hxLen.symm (ι (Fin.cast hpLen j))
          inj' := by
            intro a b hab
            apply (Fin.cast_inj hpLen).mp
            apply ι.injective
            exact (Fin.cast_inj hxLen.symm).mp hab
        }
        have hi' : ∀ j, p.get j = (List.ofFn x).get (ι' j) := by
          intro j
          calc
            p.get j = f (Fin.cast hpLen j) := hpget j
            _ = x (ι (Fin.cast hpLen j)) := hi (Fin.cast hpLen j)
            _ = (List.ofFn x).get (ι' j) := by
              rw [hxget]
              change x (ι (Fin.cast hpLen j)) =
                x (Fin.cast hxLen (Fin.cast hxLen.symm (ι (Fin.cast hpLen j))))
              rw [hxcast]
        apply hEmbedding.mpr
        exact ⟨ι', hi'⟩
    constructor
    · intro hs
      rcases hEmbedding'.mp hs with ⟨ι, hi⟩
      exact ⟨ι, fun j => (hi j).symm⟩
    · rintro ⟨ι, hi⟩
      apply hEmbedding'.mpr
      exact ⟨ι, fun j => (hi j).symm⟩
  have hEventEq :
      uniformProb (fun x : EdgeTuple V m => subgraph F (tupleGraph x)) =
        uniformProb (fun x : EdgeTuple V m => ∃ ι : Fin k ↪ Fin m,
          ∀ j, x (ι j) = f j) := by
    unfold uniformProb uniformMean
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    simp [hprobEvent x, indicator]
  have hUnion := uniformProb_iUnion_le (Ω := Ω) (ι := Fin k ↪ Fin m) hΩ
    (fun ι x => ∀ j, x (ι j) = f j)
  have hEach (ι : Fin k ↪ Fin m) :
      uniformProb (fun x : EdgeTuple V m => ∀ j, x (ι j) = f j) =
        (Fintype.card (Pair V) : ℝ) ^ (-(k : ℤ)) :=
    (h02 (Pair V) m k ι).1 f
  have hEmbed := card_fin_embedding_le k m
  have hProbNonneg : 0 ≤ (Fintype.card (Pair V) : ℝ) ^ (-(k : ℤ)) := by positivity
  have hSumBound :
      (∑ ι : Fin k ↪ Fin m,
        uniformProb (fun x : EdgeTuple V m => ∀ j, x (ι j) = f j)) ≤
      (m : ℝ)^k * (Fintype.card (Pair V) : ℝ) ^ (-(k : ℤ)) := by
    calc
      _ = (Fintype.card (Fin k ↪ Fin m) : ℝ) *
          (Fintype.card (Pair V) : ℝ) ^ (-(k : ℤ)) := by simp_rw [hEach]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hEmbed) hProbNonneg
  have hN : 0 < Fintype.card (Pair V) := Fintype.card_pos_iff.mpr hPair
  have hNne : (Fintype.card (Pair V) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hzpow :
      (Fintype.card (Pair V) : ℝ) ^ (-(k : ℤ)) =
        ((Fintype.card (Pair V) : ℝ) ^ k)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hRatio :
      (m : ℝ)^k * (Fintype.card (Pair V) : ℝ) ^ (-(k : ℤ)) =
        ((m : ℝ) / Fintype.card (Pair V))^k := by
    rw [hzpow, ← div_eq_mul_inv, div_pow]
  calc
    ThLean.BP.S3.graphProb m (fun G => subgraph F G) =
        uniformProb (fun x : EdgeTuple V m => subgraph F (tupleGraph x)) := rfl
    _ = uniformProb (fun x : EdgeTuple V m =>
        ∃ ι : Fin k ↪ Fin m, ∀ j, x (ι j) = f j) := hEventEq
    _ ≤ ∑ ι : Fin k ↪ Fin m,
        uniformProb (fun x : EdgeTuple V m => ∀ j, x (ι j) = f j) := hUnion
    _ ≤ (m : ℝ)^k * (Fintype.card (Pair V) : ℝ) ^ (-(k : ℤ)) := hSumBound
    _ = ((m : ℝ) / Fintype.card (Pair V))^edgeCount F := by
      rw [hRatio, ← hk]

end ThLean.W.S373

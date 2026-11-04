module

public import ThLean.BP.S3.Process

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S312
open ThresholdFoundations

universe u

private theorem noLoop_iff_not_isDiag {α : Type u} [DecidableEq α]
    (z : Sym2 α) : (∀ v : α, z ≠ s(v, v)) ↔ ¬ z.IsDiag := by
  induction z using Sym2.ind with
  | h a b => simp [eq_comm]

private def pairNoDiagEquiv (V : Type u) [DecidableEq V] :
    Pair V ≃ {z : Sym2 V // ¬ z.IsDiag} where
  toFun p := ⟨p.val, (noLoop_iff_not_isDiag p.val).mp p.property⟩
  invFun p := ⟨p.val, (noLoop_iff_not_isDiag p.val).mpr p.property⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl

private theorem pair_card (V : Type u) [Fintype V] :
    Fintype.card (Pair V) = (Fintype.card V).choose 2 := by
  classical
  calc
    Fintype.card (Pair V) = Fintype.card {z : Sym2 V // ¬ z.IsDiag} :=
      Fintype.card_congr (pairNoDiagEquiv V)
    _ = (Fintype.card V).choose 2 := Sym2.card_subtype_not_diag

private theorem nonempty_pair (V : Type u) [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  have hcard : 0 < Fintype.card (Pair V) := by
    rw [pair_card]
    exact Nat.choose_pos (by omega)
  exact Fintype.card_pos_iff.mp hcard

private def firstCoordinates {m M : ℕ} (hm : m ≤ M) : Fin m ↪ Fin M where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
  inj' := by
    intro a b hab
    change (⟨a.val, _⟩ : Fin M) = ⟨b.val, _⟩ at hab
    have hv : a.val = b.val := congrArg (fun z : Fin M => z.val) hab
    apply Fin.ext
    exact hv

private theorem tuplePrefix_stream {V : Type u} [Fintype V]
    (ω : EdgeStream V) (M m : ℕ) (hm : m ≤ M) :
    tuplePrefix (fun i : Fin M => ω i.val) m = processGraph ω m := by
  classical
  ext e
  change
    (Finset.univ.filter (fun i : Fin M => i.val < m ∧ ω i.val = e)).card =
      (Finset.univ.filter (fun i : Fin m => ω i.val = e)).card
  apply Finset.card_bij (fun i hi =>
    (⟨i.val, (Finset.mem_filter.mp hi).2.1⟩ : Fin m))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi.2
  · intro i hi j hj hij
    apply Fin.ext
    exact congrArg (fun z : Fin m => z.val) hij
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨firstCoordinates hm j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨j.isLt, hj⟩
    · apply Fin.ext
      rfl

private theorem uniformProb_firstCoordinates
    (h2 : ThLean.BP.S3.S3_02Statement.{u})
    {V : Type u} [Fintype V] [Nonempty (Pair V)]
    {m M : ℕ} (hm : m ≤ M) (P : EdgeTuple V m → Prop) :
    uniformProb (fun x : EdgeTuple V M => P (fun i => x (firstCoordinates hm i))) =
      uniformProb P := by
  let ι := firstCoordinates hm
  have hproj := (h2 (Pair V) M m ι).2.2.1 (fun y => indicator (P y))
  simpa [uniformProb] using hproj

private theorem sum_succ_lt (n M : ℕ) :
    (∑ k ∈ Finset.range M, if k + 1 < n then 1 else 0) = min (n - 1) M := by
  calc
    (∑ k ∈ Finset.range M, if k + 1 < n then 1 else 0) =
        ∑ k ∈ (Finset.range M).filter (fun k => k + 1 < n), (1 : ℕ) := by
          rw [← Finset.sum_filter]
    _ = ((Finset.range M).filter (fun k => k + 1 < n)).card := by simp
    _ = min (n - 1) M := by
      have hset : (Finset.range M).filter (fun k => k + 1 < n) =
          Finset.range (min (n - 1) M) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [hset, Finset.card_range]

private theorem cappedTime_coe (n M : ℕ) :
    cappedTime (n : WithTop ℕ) M = min (n - 1) M := by
  classical
  unfold cappedTime
  by_cases h : ∃ k : ℕ, (n : WithTop ℕ) = (k : WithTop ℕ)
  · rw [dite_eq_left h]
    have hfind : Nat.find h = n := WithTop.coe_injective (Nat.find_spec h).symm
    rw [hfind]
  · exact False.elim (h ⟨n, rfl⟩)

private theorem cappedLast_stream_eq_cappedTime
    (h04a : ThLean.BP.S3.S3_04aStatement.{u})
    {V : Type u} [Fintype V] (q M : ℕ) (hq : 2 ≤ q)
    (ω : EdgeStream V) :
    cappedLast q (fun i : Fin M => ω i.val) =
      cappedTime (hittingTime q ω) M := by
  classical
  have hsum :
      cappedLast q (fun i : Fin M => ω i.val) =
        ∑ k ∈ Finset.range M,
          if ((k + 1 : ℕ) : WithTop ℕ) < hittingTime q ω then 1 else 0 := by
    unfold cappedLast
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k + 1 ≤ M := by
      have := Finset.mem_range.mp hk
      omega
    rw [tuplePrefix_stream ω M (k + 1) hkm]
    have hequiv := ((h04a V q hq).2.1 ω (k + 1)).1
    rw [← hequiv]
    simp
  cases hH : hittingTime q ω with
  | top =>
      rw [hsum]
      simp [cappedTime, hH]
  | coe n =>
      rw [hsum]
      rw [hH]
      calc
        (∑ k ∈ Finset.range M,
            if ((k + 1 : ℕ) : WithTop ℕ) < (n : WithTop ℕ) then 1 else 0) =
          min (n - 1) M := by
            calc
              (∑ k ∈ Finset.range M,
                  if ((k + 1 : ℕ) : WithTop ℕ) < (n : WithTop ℕ) then 1 else 0) =
                ∑ k ∈ Finset.range M, if k + 1 < n then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  have hcmp :
                      (((k + 1 : ℕ) : WithTop ℕ) < (n : WithTop ℕ)) ↔ k + 1 < n :=
                    WithTop.coe_lt_coe
                  by_cases hkn : k + 1 < n
                  · rw [if_pos (hcmp.mpr hkn), if_pos hkn]
                  · have hnot : ¬ (((k + 1 : ℕ) : WithTop ℕ) < (n : WithTop ℕ)) :=
                      fun hlt => hkn (hcmp.mp hlt)
                    rw [if_neg hnot, if_neg hkn]
              _ = min (n - 1) M := sum_succ_lt n M
        _ = cappedTime (n : WithTop ℕ) M := (cappedTime_coe n M).symm

private theorem cappedTime_ge_iff (H : WithTop ℕ) (hH : 1 ≤ H) (m M : ℕ) (hm : m ≤ M) :
    m ≤ cappedTime H M ↔ (m : WithTop ℕ) < H := by
  cases H with
  | top => simp [cappedTime, hm]
  | coe n =>
      have hn : 1 ≤ n := by
        have hH' : ((1 : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ) := by simpa using hH
        exact WithTop.coe_le_coe.mp hH'
      have hc : cappedTime (n : WithTop ℕ) M = min (n - 1) M := cappedTime_coe n M
      have hcap :
          (m ≤ cappedTime (n : WithTop ℕ) M) ↔ m ≤ min (n - 1) M :=
        Iff.of_eq (congrArg (fun k : ℕ => m ≤ k) hc)
      exact hcap.trans <| by
        constructor
        · intro h
          have hmn : m < n := by
            have hmn' := le_trans h (Nat.min_le_left (n - 1) M)
            omega
          exact WithTop.coe_lt_coe.mpr hmn
        · intro h
          have hmn : m < n := WithTop.coe_lt_coe.mp h
          have hpred : m ≤ n - 1 := by omega
          exact (le_min_iff).2 ⟨hpred, hm⟩

private theorem cappedTime_le_iff (H : WithTop ℕ) (m M : ℕ) (hm : m < M) :
    cappedTime H M ≤ m ↔ H ≤ ((m + 1 : ℕ) : WithTop ℕ) := by
  cases H with
  | top => simp [cappedTime, hm]
  | coe n =>
      have hc : cappedTime (n : WithTop ℕ) M = min (n - 1) M := cappedTime_coe n M
      have hcap :
          (cappedTime (n : WithTop ℕ) M ≤ m) ↔ min (n - 1) M ≤ m :=
        Iff.of_eq (congrArg (fun k : ℕ => k ≤ m) hc)
      exact hcap.trans <| by
        constructor
        · intro h
          have hpred : n - 1 ≤ m := by
            have hh := (min_le_iff).mp h
            rcases hh with hleft | hright
            · exact hleft
            · omega
          have hsucc : n ≤ m + 1 := by omega
          exact WithTop.coe_le_coe.mpr hsucc
        · intro h
          have hsucc : n ≤ m + 1 := WithTop.coe_le_coe.mp h
          have hpred : n - 1 ≤ m := by omega
          exact (min_le_iff).2 (Or.inl hpred)

private theorem uniformProb_congr {A : Type*} [Fintype A]
    (P Q : A → Prop) (h : ∀ a, P a ↔ Q a) :
    uniformProb P = uniformProb Q := by
  unfold uniformProb
  congr 1
  funext a
  simp [indicator, h a]

private theorem uniformProb_not {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) :
    uniformProb (fun a => ¬ P a) = 1 - uniformProb P := by
  classical
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)))
  have hsum :
      (∑ a : A, indicator (¬ P a)) + (∑ a : A, indicator (P a)) =
        (Fintype.card A : ℝ) := by
    calc
      _ = ∑ a : A, (indicator (¬ P a) + indicator (P a)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ _a : A, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : P a <;> simp [indicator, h]
      _ = (Fintype.card A : ℝ) := by simp
  unfold uniformProb uniformMean
  field_simp [hcard]
  nlinarith [hsum]

private def extendTuple {V : Type u} (M : ℕ) (x : EdgeTuple V M)
    (e₀ : Pair V) : EdgeStream V :=
  fun n => if h : n < M then x ⟨n, h⟩ else e₀

private theorem tupleStream_graph_eq {V : Type u} [Fintype V]
    {M m : ℕ} (hm : m ≤ M) (x : EdgeTuple V M) (e₀ : Pair V) :
    processGraph (extendTuple M x e₀) m =
      tupleGraph (fun i : Fin m => x (firstCoordinates hm i)) := by
  classical
  unfold processGraph
  congr 1
  funext i
  have hiM : i.val < M := lt_of_lt_of_le i.isLt hm
  simp only [extendTuple, dif_pos hiM, firstCoordinates]
  exact congrArg x (Fin.ext rfl)

private theorem cappedLast_stream_ge_iff
    (h04a : ThLean.BP.S3.S3_04aStatement.{u})
    {V : Type u} [Fintype V] (q M m : ℕ) (hq : 2 ≤ q)
    (ω : EdgeStream V) (hm : m ≤ M) :
    m ≤ cappedLast q (fun i : Fin M => ω i.val) ↔
      (m : WithTop ℕ) < hittingTime q ω := by
  rw [cappedLast_stream_eq_cappedTime h04a q M hq ω]
  exact cappedTime_ge_iff (hittingTime q ω) ((h04a V q hq).1 ω) m M hm

private theorem cappedLast_stream_le_iff
    (h04a : ThLean.BP.S3.S3_04aStatement.{u})
    {V : Type u} [Fintype V] (q M m : ℕ) (hq : 2 ≤ q)
    (ω : EdgeStream V) (hm : m < M) :
    cappedLast q (fun i : Fin M => ω i.val) ≤ m ↔
      hittingTime q ω ≤ ((m + 1 : ℕ) : WithTop ℕ) := by
  rw [cappedLast_stream_eq_cappedTime h04a q M hq ω]
  exact cappedTime_le_iff (hittingTime q ω) m M hm

private theorem cappedLast_tuple_ge_iff
    (h04a : ThLean.BP.S3.S3_04aStatement.{u})
    {V : Type u} [Fintype V] [Nonempty (Pair V)]
    (q M m : ℕ) (hq : 2 ≤ q) (hm : m ≤ M) (x : EdgeTuple V M) :
    m ≤ cappedLast q x ↔
      Colorable q (tupleGraph (fun i : Fin m => x (firstCoordinates hm i))) := by
  classical
  let ω := extendTuple M x (Classical.choice (inferInstance : Nonempty (Pair V)))
  have hx : (fun i : Fin M => ω i.val) = x := by
    funext i
    simp [ω, extendTuple, i.isLt]
  calc
    m ≤ cappedLast q x ↔
        m ≤ cappedLast q (fun i : Fin M => ω i.val) := by rw [hx]
    _ ↔ (m : WithTop ℕ) < hittingTime q ω :=
      cappedLast_stream_ge_iff h04a q M m hq ω hm
    _ ↔ Colorable q (processGraph ω m) :=
      ((h04a V q hq).2.1 ω m).1
    _ ↔ Colorable q (tupleGraph (fun i : Fin m => x (firstCoordinates hm i))) := by
      rw [tupleStream_graph_eq hm x (Classical.choice (inferInstance : Nonempty (Pair V)))]

private theorem cappedTail_eq_processSurvival
    (h04a : ThLean.BP.S3.S3_04aStatement.{u})
    (h2 : ThLean.BP.S3.S3_02Statement.{u})
    {V : Type u} [Fintype V] [Nonempty (Pair V)]
    (q M m : ℕ) (hq : 2 ≤ q) (hm : m ≤ M) :
    cappedTail (V := V) q M m = processSurvival (V := V) q m := by
  classical
  letI : Nonempty (EdgeTuple V M) :=
    ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair V))⟩
  letI : Nonempty (EdgeTuple V m) :=
    ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair V))⟩
  calc
    cappedTail (V := V) q M m =
        uniformProb (fun x : EdgeTuple V M => m ≤ cappedLast q x) := rfl
    _ = uniformProb (fun x : EdgeTuple V M =>
        Colorable q (tupleGraph (fun i : Fin m => x (firstCoordinates hm i)))) := by
          apply uniformProb_congr
          intro x
          exact cappedLast_tuple_ge_iff h04a q M m hq hm x
    _ = uniformProb (fun y : EdgeTuple V m => Colorable q (tupleGraph y)) :=
          uniformProb_firstCoordinates h2 hm (fun y => Colorable q (tupleGraph y))
    _ = processSurvival (V := V) q m := by
          unfold processSurvival survival
          simp [uniformProb, uniformMean, indicator]

theorem S3_05Statement_of_deps
    (h04a : ThLean.BP.S3.S3_04aStatement.{u})
    (h2 : ThLean.BP.S3.S3_02Statement.{u}) :
    ThLean.BP.S3.S3_05Statement.{u} := by
  intro V _ q M hq hV
  letI : Nonempty (Pair V) := nonempty_pair V hV
  letI : Nonempty (EdgeTuple V M) :=
    ⟨fun _ => Classical.choice (inferInstance : Nonempty (Pair V))⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold cappedLast
    calc
      (∑ k ∈ Finset.range M,
          if Colorable q (tuplePrefix x (k + 1)) then 1 else 0) ≤
        ∑ k ∈ Finset.range M, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro k hk
          split_ifs <;> omega
      _ = M := by simp
  · intro ω m
    dsimp only
    constructor
    · intro hm
      exact cappedLast_stream_ge_iff h04a q M m hq ω hm
    · intro hm
      exact cappedLast_stream_le_iff h04a q M m hq ω hm
  · intro m hm
    exact cappedTail_eq_processSurvival h04a h2 q M m hq hm
  · intro m hm
    have hcomp :
        cappedCDF (V := V) q M m = 1 - cappedTail (V := V) q M (m + 1) := by
      unfold cappedCDF cappedTail
      have htailcomp :
          uniformProb (fun x : EdgeTuple V M => m + 1 ≤ cappedLast q x) =
            uniformProb (fun x : EdgeTuple V M => ¬ cappedLast q x ≤ m) := by
        apply uniformProb_congr
        intro x
        omega
      calc
        uniformProb (fun x : EdgeTuple V M => cappedLast q x ≤ m) =
            1 - uniformProb (fun x : EdgeTuple V M => ¬ cappedLast q x ≤ m) :=
              by linarith [uniformProb_not (fun x : EdgeTuple V M => cappedLast q x ≤ m)]
        _ = 1 - uniformProb (fun x : EdgeTuple V M => m + 1 ≤ cappedLast q x) := by
              rw [htailcomp]
    rw [hcomp]
    have hm' : m + 1 ≤ M := by omega
    rw [cappedTail_eq_processSurvival h04a h2 q M (m + 1) hq hm']
  · intro m ω ω' hagree
    have hx : (fun i : Fin M => ω i.val) = (fun i : Fin M => ω' i.val) := by
      funext i
      exact hagree i.val i.isLt
    change (cappedLast q (fun i : Fin M => ω i.val) ≤ m) ↔
      (cappedLast q (fun i : Fin M => ω' i.val) ≤ m)
    rw [hx]

end ThLean.W.S312

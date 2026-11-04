module

public import ThLean.BP.S4.Deletion

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S421

private theorem uniformMeanBetween {A : Type}
    (i j : Fintype A) (hne : Nonempty A)
    (hFinite : PreFiniteLawsStatement.{0,0}) (f : A → ℝ) :
    @uniformMean A i f = @uniformMean A j f := by
  exact @hFinite.1 A A i j hne hne (Equiv.refl A) f

private theorem uniformMeanIndicatorMul {A : Type} (i : Fintype A)
    (P : A → Prop) (c : ℝ) :
    @uniformMean A i (fun a => indicator (P a) * c) =
      @uniformProb A i P * c := by
  simp only [uniformProb, uniformMean]
  rw [← Finset.sum_mul]
  ring

@[instance_reducible] private def terminalPairFintype (n : ℕ) : Fintype (Pair (Fin n)) :=
  @Subtype.fintype (Sym2 (Fin n)) (fun e => ∀ v : Fin n, e ≠ s(v, v))
    (fun a => @Nat.decidableForallFin n
      (fun v : Fin n => a ≠ s(v, v))
      (fun a_1 : Fin n => @instDecidableNot (a = s(a_1, a_1))
        (@Sym2.instDecidableEq (Fin n) (instDecidableEqFin n) a (s(a_1, a_1)))))
    (@Sym2.instFintype (Fin n) (Fin.fintype n))

@[instance_reducible] private def kappaPairFintype (n : ℕ) : Fintype (Pair (Fin n)) :=
  @Subtype.fintype (Sym2 (Fin n)) (fun e => ∀ v : Fin n, e ≠ s(v, v))
    (fun a => @Fintype.decidableForallFintype (Fin n)
      (fun v : Fin n => a ≠ s(v, v))
      (fun a_1 : Fin n => @instDecidableNot (a = s(a_1, a_1))
        (@Sym2.instDecidableEq (Fin n)
          (fun a b => Classical.propDecidable (a = b)) a (s(a_1, a_1))))
      (Fin.fintype n))
    (@Sym2.instFintype (Fin n) (Fin.fintype n))

@[instance_reducible] private def tupleFintypeOf {V : Type} [Fintype V]
    (i : Fintype (Pair V)) (k : ℕ) : Fintype (EdgeTuple V k) := by
  letI : Fintype (Pair V) := i
  exact inferInstance

private theorem finPair_nonempty {n : ℕ} (hn : 2 ≤ n) :
    Nonempty (Pair (Fin n)) := by
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  have h01 : v0 ≠ v1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  refine ⟨⟨s(v0, v1), ?_⟩⟩
  intro v hv
  rcases Sym2.eq_iff.mp hv with ⟨h0, h1⟩ | ⟨h0, h1⟩
  all_goals exact h01 (h0.trans h1.symm)

private theorem terminalStepFactor (hFrozen : PreFrozenStatement.{0})
    (hFinite : PreFiniteLawsStatement.{0,0}) (q n k : ℕ)
    (hq : 3 ≤ q) (hn : 2*q ≤ n) (F : ℕ → MGraph (Fin n) → ℝ)
    (tFrozen tTerm : Fintype (EdgeTuple (Fin n) k)) :
    @uniformMean (EdgeTuple (Fin n) k) tFrozen
        (fun x => @uniformMean (Pair (Fin n)) (kappaPairFintype n)
          (fun e => if Colorable q (tupleGraph x) ∧
            ¬ Colorable q (addPair (tupleGraph x) e)
            then F (k+1) (tupleGraph x) else 0)) =
      @uniformMean (EdgeTuple (Fin n) k) tTerm
        (fun x => kappa q (tupleGraph x) * F (k+1) (tupleGraph x)) := by
  have hcard : 2 ≤ Fintype.card (Fin n) := by simpa using (show 2 ≤ n by omega)
  have hpre := hFrozen (Fin n) q hq hcard
  have hPair : Nonempty (Pair (Fin n)) := finPair_nonempty (by omega)
  have hTuple : Nonempty (EdgeTuple (Fin n) k) :=
    ⟨fun _ => Classical.choice hPair⟩
  have hEdge (x : EdgeTuple (Fin n) k) :
      @uniformMean (Pair (Fin n)) (kappaPairFintype n)
        (fun e => if Colorable q (tupleGraph x) ∧
          ¬ Colorable q (addPair (tupleGraph x) e)
          then F (k+1) (tupleGraph x) else 0) =
        kappa q (tupleGraph x) * F (k+1) (tupleGraph x) := by
    let A : Pair (Fin n) → Prop := fun e =>
      Colorable q (tupleGraph x) ∧
        ¬ Colorable q (addPair (tupleGraph x) e)
    have hfun : (fun e : Pair (Fin n) =>
        if A e then F (k+1) (tupleGraph x) else 0) =
        (fun e => indicator (A e) * F (k+1) (tupleGraph x)) := by
      funext e
      by_cases h : A e <;> simp [indicator, h]
    calc
      _ = @uniformMean (Pair (Fin n)) (kappaPairFintype n)
          (fun e => indicator (A e) * F (k+1) (tupleGraph x)) :=
        congrArg (@uniformMean (Pair (Fin n)) (kappaPairFintype n)) hfun
      _ = @uniformProb (Pair (Fin n)) (kappaPairFintype n) A *
            F (k+1) (tupleGraph x) :=
        uniformMeanIndicatorMul (kappaPairFintype n) A _
      _ = kappa q (tupleGraph x) * F (k+1) (tupleGraph x) := by
        have hprob : @uniformProb (Pair (Fin n)) (kappaPairFintype n) A =
            kappa q (tupleGraph x) := by
          simpa [A] using hpre.2.1 (tupleGraph x)
        rw [hprob]
  calc
    _ = @uniformMean (EdgeTuple (Fin n) k) tTerm
        (fun x => @uniformMean (Pair (Fin n)) (kappaPairFintype n)
          (fun e => if Colorable q (tupleGraph x) ∧
            ¬ Colorable q (addPair (tupleGraph x) e)
            then F (k+1) (tupleGraph x) else 0)) :=
      uniformMeanBetween tFrozen tTerm hTuple hFinite _
    _ = @uniformMean (EdgeTuple (Fin n) k) tTerm
        (fun x => kappa q (tupleGraph x) * F (k+1) (tupleGraph x)) :=
      congrArg (@uniformMean (EdgeTuple (Fin n) k) tTerm) (funext hEdge)

theorem S4_RED_08AStatement_of_deps (hFrozen : PreFrozenStatement.{0})
    (hFinite : PreFiniteLawsStatement.{0,0}) :
    ThLean.BP.S4.S4_RED_08AStatement := by
  intro q n hq hn L U hLU F
  unfold ThLean.BP.S4.terminalReal
  apply Finset.sum_congr rfl
  intro k hk
  let tFrozen := tupleFintypeOf (kappaPairFintype n) k
  let tTerm := tupleFintypeOf (terminalPairFintype n) k
  simpa only [kappaPairFintype, terminalPairFintype, tFrozen, tTerm, tupleFintypeOf] using
    terminalStepFactor hFrozen hFinite q n k hq hn F tFrozen tTerm

example (hFrozen : PreFrozenStatement.{0}) (hFinite : PreFiniteLawsStatement.{0,0}) :
    ThLean.BP.S4.S4_RED_08AStatement :=
  S4_RED_08AStatement_of_deps hFrozen hFinite


end ThLean.W.S421

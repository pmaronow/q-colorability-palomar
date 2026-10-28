import ThLean.W.SA51S.Means

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA51S
open ThresholdFoundations ThLean.BP.SA

def edgeOp (n : ℕ) : Module.End ℝ (MGraph (Fin n) → ℝ) :=
  averageOp (fun (G : MGraph (Fin n)) (xy : Fin n × Fin n) => addEdge G s(xy.1, xy.2))

lemma edgeOp_iterate (n m : ℕ) :
    ⇑(edgeOp n ^ m) = (⇑(edgeOp n))^[m] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Function.iterate_succ', ← ih]
    rfl

lemma addEdge_add {V : Type} (G H : MGraph V) (e : Sym2 V) :
    addEdge G e + H = G + addEdge H e := by
  classical
  funext d
  by_cases hd : d = e <;> simp [addEdge, hd, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

lemma ordered_cons {n m : ℕ} (a : Fin n × Fin n) (x : Fin m → Fin n × Fin n) :
    orderedTupleGraph (Fin.cons a x) = addEdge (orderedTupleGraph x) s(a.1, a.2) := by
  funext e
  unfold orderedTupleGraph
  rw [Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← Finset.card_filter]
  by_cases he : e = s(a.1, a.2)
  all_goals simp [addEdge, he, Ne.symm, Nat.add_comm]
  congr 1
  ext i
  simp

@[simp] lemma ordered_nil (n : ℕ) (x : Fin 0 → Fin n × Fin n) :
    orderedTupleGraph x = 0 := by
  ext e
  simp [orderedTupleGraph]

lemma edgeOp_pow (n m : ℕ) (f : MGraph (Fin n) → ℝ) (G : MGraph (Fin n)) :
    (edgeOp n ^ m) f G = uniformMean (fun x : Fin m → Fin n × Fin n =>
      f (G + orderedTupleGraph x)) := by
  induction m generalizing G with
  | zero => simp [uniformMean]
  | succ m ih =>
    rw [pow_succ']
    change uniformMean (fun a : Fin n × Fin n =>
      (edgeOp n ^ m) f (addEdge G s(a.1, a.2))) = _
    simp_rw [ih]
    rw [mean_cons]
    apply mean_congr
    intro a
    apply mean_congr
    intro x
    rw [ordered_cons, addEdge_add]

lemma global_iterate (n₁ n₂ q m : ℕ) :
    ((globalStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0 =
      uniformProb (fun x : Fin m → Fin (n₁+n₂) × Fin (n₁+n₂) =>
        Colorable q (orderedTupleGraph x)) := by
  change ((⇑(edgeOp (n₁+n₂)))^[m]) (fun H => indicator (Colorable q H)) 0 = _
  rw [← edgeOp_iterate]
  simpa [uniformProb] using edgeOp_pow (n₁+n₂) m
    (fun H => indicator (Colorable q H)) 0

lemma global_mixture (q n₁ n₂ : ℕ) (c : ℝ) :
    poissonMixture (c * (n₁+n₂ : ℕ))
      (fun m => ((globalStep n₁ n₂)^[m]) (fun H => indicator (Colorable q H)) 0) =
      rho q (n₁+n₂) c := by
  simp only [poissonMixture, rho, global_iterate]

end ThLean.W.SA51S

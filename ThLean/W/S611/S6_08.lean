module

public import ThLean.BP.S6.Foundation

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S6

namespace ThLean.W.S611

private theorem tupleGraph_reindex {n m : ℕ} (x : Hist n m)
    (σ : Equiv.Perm (Fin m)) :
    tupleGraph (fun i => x (σ i)) = tupleGraph x := by
  classical
  funext e
  simp only [tupleGraph]
  apply Finset.card_bijective σ σ.bijective
  intro i
  simp

private theorem tupleGraph_count_last {n k : ℕ} (x : Hist n (k + 1)) (e : Sym2 (Fin n)) :
    (Finset.univ.filter (fun i : Fin (k + 1) => (x i).val = e)).card =
      (Finset.univ.filter (fun i : Fin k => (x i.castSucc).val = e)).card +
        (if (x (Fin.last k)).val = e then 1 else 0) := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp

private theorem erase_last_graph {n k : ℕ} (x : Hist n (k + 1)) :
    erasePair (tupleGraph x) (x (Fin.last k)) =
      tupleGraph (fun i : Fin k => x i.castSucc) := by
  classical
  funext e
  have hc := tupleGraph_count_last x e
  by_cases he : (x (Fin.last k)).val = e
  · subst e
    have hc' : tupleGraph x (x (Fin.last k)).val =
        tupleGraph (fun i : Fin k => x i.castSucc) (x (Fin.last k)).val + 1 := by
      rw [tupleGraph, tupleGraph]
      simpa using hc
    simp [erasePair, eraseEdge, hc']
  · have hne : e ≠ (x (Fin.last k)).val := Ne.symm he
    have hc' : tupleGraph x e = tupleGraph (fun i : Fin k => x i.castSucc) e := by
      rw [tupleGraph, tupleGraph]
      simpa [he] using hc
    simp [erasePair, eraseEdge, hne, hc']

private theorem last_coordinate_mean {n k : ℕ} (hn : 3 ≤ n)
    (hb : ThLean.BP.S6.S6_01bStatement) (h : Graph n → Edge n → ℝ) :
    uniformMean (fun x : Hist n (k + 1) =>
      h (erasePair (tupleGraph x) (x (Fin.last k))) (x (Fin.last k))) =
      meanGraph k (fun G => uniformMean (h G)) := by
  rcases hb n hn with ⟨_, havg⟩
  let J : Hist n k → ℝ := fun _ => 1
  let Z : Hist n k → Edge n → ℝ := fun x e => h (tupleGraph x) e
  have hs := havg k J Z
  calc
    uniformMean (fun x : Hist n (k + 1) =>
        h (erasePair (tupleGraph x) (x (Fin.last k))) (x (Fin.last k)))
      = uniformMean (fun x : Hist n (k + 1) =>
          J (takePrefix (Nat.le_succ k) x) *
            Z (takePrefix (Nat.le_succ k) x) (x ⟨k, Nat.lt_succ_self k⟩)) := by
          congr 1
          funext x
          rw [erase_last_graph]
          simp only [J, Z]
          have hpref : (fun i : Fin k => x i.castSucc) = takePrefix (Nat.le_succ k) x := by
            funext i
            rfl
          rw [hpref]
          have hlast : x (Fin.last k) = x ⟨k, Nat.lt_succ_self k⟩ := by
            congr 1
          rw [hlast]
          simp
    _ = uniformMean (fun x : Hist n k => J x * uniformMean (Z x)) := hs
    _ = meanGraph k (fun G => uniformMean (h G)) := by
          simp [J, Z, meanGraph, one_mul]

private theorem coordinate_mean {n k : ℕ} (hn : 3 ≤ n)
    (hb : ThLean.BP.S6.S6_01bStatement) (h : Graph n → Edge n → ℝ)
    (i : Fin (k + 1)) :
    uniformMean (fun x : Hist n (k + 1) =>
      h (erasePair (tupleGraph x) (x i)) (x i)) =
      meanGraph k (fun G => uniformMean (h G)) := by
  let σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap i (Fin.last k)
  let ρ : Hist n (k + 1) ≃ Hist n (k + 1) :=
    Equiv.arrowCongr σ.symm (Equiv.refl (Edge n))
  have hgraph (x : Hist n (k + 1)) :
      tupleGraph (fun j => x (σ j)) = tupleGraph x := tupleGraph_reindex x σ
  have hlast (x : Hist n (k + 1)) : x (σ (Fin.last k)) = x i := by
    simp [σ, Equiv.swap_apply_right]
  have hintegrand (x : Hist n (k + 1)) :
      h (erasePair (tupleGraph x) (x i)) (x i) =
        h (erasePair (tupleGraph (ρ x)) ((ρ x) (Fin.last k))) ((ρ x) (Fin.last k)) := by
    change h (erasePair (tupleGraph x) (x i)) (x i) =
      h (erasePair (tupleGraph (fun j => x (σ j))) (x (σ (Fin.last k))))
        (x (σ (Fin.last k)))
    rw [hgraph x, hlast x]
  have hsum := Fintype.sum_equiv ρ
    (fun x : Hist n (k + 1) => h (erasePair (tupleGraph x) (x i)) (x i))
    (fun x => h (erasePair (tupleGraph x) (x (Fin.last k))) (x (Fin.last k)))
    hintegrand
  unfold uniformMean
  rw [hsum]
  exact last_coordinate_mean hn hb h

theorem S6_08Statement_of_deps (hb : ThLean.BP.S6.S6_01bStatement) :
    ThLean.BP.S6.S6_08Statement := by
  intro n m hn hm h
  cases m with
  | zero => omega
  | succ k =>
      have heach (i : Fin (k + 1)) :
          uniformMean (fun x : Hist n (k + 1) =>
            h (erasePair (tupleGraph x) (x i)) (x i)) =
          meanGraph k (fun G => uniformMean (h G)) := coordinate_mean hn hb h i
      calc
        uniformMean (fun x : Hist n (k + 1) =>
            ∑ i : Fin (k + 1), h (erasePair (tupleGraph x) (x i)) (x i))
          = ∑ i : Fin (k + 1), uniformMean (fun x : Hist n (k + 1) =>
              h (erasePair (tupleGraph x) (x i)) (x i)) := by
                unfold uniformMean
                rw [Finset.sum_comm, Finset.sum_div]
        _ = ∑ _i : Fin (k + 1), meanGraph k (fun G => uniformMean (h G)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact heach i
        _ = ((k + 1 : ℕ) : ℝ) * meanGraph k (fun G => uniformMean (h G)) := by
              simp
        _ = ((k + 1 : ℕ) : ℝ) * meanGraph k (fun G => uniformMean (h G)) := by
              simp [meanGraph]

end ThLean.W.S611

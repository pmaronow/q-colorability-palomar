import ThLean.BP.S3.Cycles

noncomputable section
open scoped BigOperators
universe u
namespace ThLean.W.S369
open ThresholdFoundations
open ThLean.BP.S3

variable {V : Type u} [Fintype V]

/-- Counting the filtered list at each edge counts each list position once. -/
theorem edgeCount_edgesGraph (xs : List (Sym2 V)) :
    edgeCount (edgesGraph xs) = xs.length := by
  classical
  induction xs with
  | nil => simp [edgeCount, edgesGraph]
  | cons x xs ih =>
      change (∑ e : Sym2 V, (List.filter (fun f => f = e) (x :: xs)).length) = xs.length + 1
      have hpoint (e : Sym2 V) :
          (List.filter (fun f => f = e) (x :: xs)).length =
            (List.filter (fun f => f = e) xs).length + (if x = e then 1 else 0) := by
        by_cases h : x = e <;> simp [h]
      rw [Finset.sum_congr rfl (fun e _ => hpoint e), Finset.sum_add_distrib]
      change edgeCount (edgesGraph xs) +
        (∑ e : Sym2 V, if x = e then 1 else 0) = xs.length + 1
      rw [ih]
      simp

omit [Fintype V] in
theorem consecutiveEdges_length (xs : List V) :
    (consecutiveEdges xs).length = xs.length - 1 := by
  simp [consecutiveEdges, List.length_zip, List.length_tail]

theorem thetaCode_edgeCount {k : ℕ} (hk : 0 < k)
    (j₁ j₂ j₃ : ℕ) (labels : Fin k → V)
    (hj₁ : 1 ≤ j₁) (hj₂ : 1 ≤ j₂) (hj₃ : 1 ≤ j₃)
    (hsum : j₁ + j₂ + j₃ = k + 1) :
    edgeCount (thetaCode hk j₁ j₂ j₃ labels) = k + 1 := by
  classical
  rw [thetaCode, edgeCount_edgesGraph]
  simp only [List.length_append, consecutiveEdges_length,
    List.length_cons, List.length_nil, List.length_append, List.length_map,
    List.length_range]
  omega

end ThLean.W.S369

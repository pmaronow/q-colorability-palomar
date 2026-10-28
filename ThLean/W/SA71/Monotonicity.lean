import ThLean.BP.SA.Transfer

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ThLean.W.SA71

open ThresholdFoundations

private def colorLayer (q n m : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  by
    classical
    exact (simpleGraphsWithEdges (V := Fin n) m).filter
      (fun E => Colorable q (simpleGraph E))

private theorem simpleGraphsWithEdges_eq_powersetCard (n m : ℕ) :
    simpleGraphsWithEdges (V := Fin n) m =
      (completeEdges (V := Fin n)).powersetCard m := by
  ext E
  simp [simpleGraphsWithEdges, Finset.mem_powersetCard]

private def internalPairEquiv (n : ℕ) :
    Pair (Fin n) ≃ ↥(completeEdges (V := Fin n)) where
  toFun e := ⟨e.1, by simpa [completeEdges] using e.2⟩
  invFun e := ⟨e.1, by simpa [completeEdges] using e.2⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

private def lowerIncidences (q n m : ℕ) :
    Finset (Σ A : ↥(colorLayer q n m), ↥(completeEdges (V := Fin n) \ A.1)) :=
  (colorLayer q n m).attach.sigma
    (fun A => (completeEdges (V := Fin n) \ A.1).attach)

private def upperIncidences (q n m : ℕ) :
    Finset (Σ B : ↥(colorLayer q n (m + 1)), ↥B.1) :=
  (colorLayer q n (m + 1)).attach.sigma (fun B => B.1.attach)

private def eraseMarkedEdge {q n m : ℕ}
    (z : Σ B : ↥(colorLayer q n (m + 1)), ↥B.1) :
    Σ A : ↥(colorLayer q n m), ↥(completeEdges (V := Fin n) \ A.1) := by
  let B := z.1.1
  let e := z.2.1
  have heB : e ∈ B := z.2.2
  have hlayer : B ∈ colorLayer q n (m + 1) := z.1.2
  have hB : B ∈ simpleGraphsWithEdges (V := Fin n) (m + 1) :=
    (Finset.mem_filter.mp hlayer).1
  rw [simpleGraphsWithEdges_eq_powersetCard] at hB
  have hBsub : B ⊆ completeEdges (V := Fin n) := (Finset.mem_powersetCard.mp hB).1
  have hBcard : B.card = m + 1 := (Finset.mem_powersetCard.mp hB).2
  have hcolB : Colorable q (simpleGraph B) := (Finset.mem_filter.mp hlayer).2
  have hAsub : B.erase e ⊆ completeEdges (V := Fin n) := (Finset.erase_subset _ _).trans hBsub
  have hAcard : (B.erase e).card = m := by
    rw [Finset.card_erase_of_mem heB, hBcard]
    omega
  have hcolA : Colorable q (simpleGraph (B.erase e)) := by
    obtain ⟨σ, hσ⟩ := hcolB
    refine ⟨σ, ?_⟩
    intro u v huv
    have hmemErase : s(u, v) ∈ B.erase e := by
      by_contra hnot
      simp [simpleGraph, hnot] at huv
    have hmemB : s(u, v) ∈ B := Finset.mem_of_mem_erase hmemErase
    have hpos : 0 < simpleGraph B (s(u, v)) := by
      simp [simpleGraph, hmemB]
    exact hσ u v hpos
  refine ⟨⟨B.erase e, Finset.mem_filter.mpr ⟨?_, hcolA⟩⟩,
    ⟨e, Finset.mem_sdiff.mpr ⟨hBsub heB, Finset.notMem_erase e B⟩⟩⟩
  rw [simpleGraphsWithEdges_eq_powersetCard]
  exact Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩

private theorem eraseMarkedEdge_injective {q n m : ℕ} :
    Set.InjOn (eraseMarkedEdge (q := q) (n := n) (m := m))
      (upperIncidences q n m : Set _) := by
  intro x hx y hy hxy
  obtain ⟨B, e⟩ := x
  obtain ⟨C, f⟩ := y
  have heB : e.1 ∈ B.1 := e.2
  have hfC : f.1 ∈ C.1 := f.2
  have hA : B.1.erase e.1 = C.1.erase f.1 := by
    have := congrArg (fun z : Σ A : ↥(colorLayer q n m),
        ↥(completeEdges (V := Fin n) \ A.1) => z.1.1) hxy
    simpa [eraseMarkedEdge] using this
  have hef : e.1 = f.1 := by
    have := congrArg (fun z : Σ A : ↥(colorLayer q n m),
        ↥(completeEdges (V := Fin n) \ A.1) => z.2.1) hxy
    simpa [eraseMarkedEdge] using this
  have hfC' : e.1 ∈ C.1 := by simp [hef]
  have hBC : B.1 = C.1 := by
    calc
      B.1 = insert e.1 (B.1.erase e.1) := (Finset.insert_erase heB).symm
      _ = insert e.1 (C.1.erase e.1) := by rw [hA, ← hef]
      _ = C.1 := Finset.insert_erase hfC'
  have hBC' : B = C := Subtype.ext hBC
  subst C
  have hef' : e = f := Subtype.ext hef
  subst f
  rfl

private theorem card_lowerIncidences (q n m : ℕ) :
    (lowerIncidences q n m).card =
      (colorLayer q n m).card * ((completeEdges (V := Fin n)).card - m) := by
  classical
  rw [lowerIncidences, Finset.card_sigma]
  have hfiber : ∀ A : ↥(colorLayer q n m),
      (completeEdges (V := Fin n) \ A.1).card =
        (completeEdges (V := Fin n)).card - m := by
    intro A
    have hA := (Finset.mem_filter.mp A.2).1
    rw [simpleGraphsWithEdges_eq_powersetCard] at hA
    have hsub : A.1 ⊆ completeEdges (V := Fin n) :=
      (Finset.mem_powersetCard.mp hA).1
    have hcard : A.1.card = m := (Finset.mem_powersetCard.mp hA).2
    rw [Finset.card_sdiff_of_subset hsub, hcard]
  calc
    _ = ∑ A ∈ (colorLayer q n m).attach, ((completeEdges (V := Fin n) \ A.1).card) := by
      simp only [Finset.card_attach]
    _ = ∑ A ∈ (colorLayer q n m).attach,
        ((completeEdges (V := Fin n)).card - m) := by
      apply Finset.sum_congr rfl
      intro A hA
      exact hfiber A
    _ = (colorLayer q n m).card * ((completeEdges (V := Fin n)).card - m) := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      simp

private theorem card_upperIncidences (q n m : ℕ) :
    (upperIncidences q n m).card =
      (colorLayer q n (m + 1)).card * (m + 1) := by
  classical
  rw [upperIncidences, Finset.card_sigma]
  calc
    _ = ∑ B ∈ (colorLayer q n (m + 1)).attach, B.1.card := by
      simp
    _ = ∑ B ∈ (colorLayer q n (m + 1)).attach, (m + 1) := by
      apply Finset.sum_congr rfl
      intro B hB
      have hmem : B.1 ∈ simpleGraphsWithEdges (V := Fin n) (m + 1) :=
        (Finset.mem_filter.mp B.2).1
      rw [simpleGraphsWithEdges_eq_powersetCard] at hmem
      exact (Finset.mem_powersetCard.mp hmem).2
    _ = (colorLayer q n (m + 1)).card * (m + 1) := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      simp

private theorem simpleGraphsWithEdges_card (n m : ℕ) :
    (simpleGraphsWithEdges (V := Fin n) m).card =
      Nat.choose (completeEdges (V := Fin n)).card m := by
  rw [simpleGraphsWithEdges_eq_powersetCard]
  exact Finset.card_powersetCard m (completeEdges (V := Fin n))

private theorem colorable_succ_count_le (q n m : ℕ) :
    (colorLayer q n (m + 1)).card * (m + 1) ≤
      (colorLayer q n m).card * ((completeEdges (V := Fin n)).card - m) := by
  classical
  have hmap : (upperIncidences q n m).image (eraseMarkedEdge (q := q) (n := n) (m := m)) ⊆
      lowerIncidences q n m := by
    intro z hz
    rw [lowerIncidences, Finset.mem_sigma]
    exact ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩
  have hcard : (upperIncidences q n m).card ≤ (lowerIncidences q n m).card := by
    calc
      (upperIncidences q n m).card =
          ((upperIncidences q n m).image (eraseMarkedEdge (q := q) (n := n) (m := m))).card := by
            symm
            exact Finset.card_image_iff.mpr (eraseMarkedEdge_injective (q := q) (n := n) (m := m))
      _ ≤ (lowerIncidences q n m).card := Finset.card_le_card hmap
  rw [card_upperIncidences, card_lowerIncidences] at hcard
  exact hcard

private theorem simpleProbability_succ_le (q n m : ℕ)
    (hm : m + 1 ≤ (completeEdges (V := Fin n)).card) :
    simpleProbability (V := Fin n) q (m + 1) ≤ simpleProbability (V := Fin n) q m := by
  classical
  let N := (completeEdges (V := Fin n)).card
  let a := (colorLayer q n m).card
  let b := (colorLayer q n (m + 1)).card
  let d := Nat.choose N m
  let c := Nat.choose N (m + 1)
  have hvalid : m ≤ N := by omega
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.choose_pos hvalid
  have hcpos : 0 < c := by
    dsimp [c]
    exact Nat.choose_pos hm
  have hincNat : b * (m + 1) ≤ a * (N - m) := by
    dsimp [a, b, N]
    exact colorable_succ_count_le q n m
  have hinc : (b : ℝ) * (m + 1 : ℝ) ≤ (a : ℝ) * (N - m : ℝ) := by
    exact_mod_cast hincNat
  have hchooseNat : c * (m + 1) = d * (N - m) := by
    dsimp [c, d, N]
    exact Nat.choose_succ_right_eq _ _
  have hchoose : (c : ℝ) * (m + 1 : ℝ) = (d : ℝ) * (N - m : ℝ) := by
    exact_mod_cast hchooseNat
  have hx : (0 : ℝ) < (m + 1 : ℝ) := by positivity
  have hcross : (b : ℝ) * d ≤ (a : ℝ) * c := by
    have hmul := mul_le_mul_of_nonneg_right hinc (show (0 : ℝ) ≤ d by positivity)
    have hmul' : ((b : ℝ) * d) * (m + 1 : ℝ) ≤ ((a : ℝ) * c) * (m + 1 : ℝ) := by
      calc
        ((b : ℝ) * d) * (m + 1 : ℝ) = ((b : ℝ) * (m + 1 : ℝ)) * d := by ring
        _ ≤ ((a : ℝ) * (N - m : ℝ)) * d := hmul
        _ = ((a : ℝ) * c) * (m + 1 : ℝ) := by
          calc
            _ = (a : ℝ) * ((d : ℝ) * (N - m : ℝ)) := by ring
            _ = (a : ℝ) * ((c : ℝ) * (m + 1 : ℝ)) := by rw [hchoose.symm]
            _ = _ := by ring
    exact (mul_le_mul_iff_of_pos_right hx).mp hmul'
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hcreal : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hratio : (b : ℝ) / c ≤ (a : ℝ) / d := (div_le_div_iff₀ hcreal hdreal).2 hcross
  have hdenM : ((simpleGraphsWithEdges (V := Fin n) m).card : ℝ) = d := by
    simp [simpleGraphsWithEdges_card, d, N]
  have hdenS : ((simpleGraphsWithEdges (V := Fin n) (m + 1)).card : ℝ) = c := by
    simp [simpleGraphsWithEdges_card, c, N]
  simpa [simpleProbability, colorLayer, hdenM, hdenS, a, b] using hratio

theorem SA_X53Statement_of_deps
    (hPair : ThresholdFoundations.PairBridgeStatement) :
    ThLean.BP.SA.SA_X53Statement := by
  intro q n m m' hq hn hmm hm'
  have hN : m' ≤ (completeEdges (V := Fin n)).card := by
    have hpair : Fintype.card (Pair (Fin n)) = n.choose 2 := (hPair n).2.1
    have hcard : Fintype.card (Pair (Fin n)) =
        (completeEdges (V := Fin n)).card := by
      calc
        _ = Fintype.card ↥(completeEdges (V := Fin n)) :=
          Fintype.card_congr (internalPairEquiv n)
        _ = _ := by simp
    calc
      m' ≤ n.choose 2 := hm'
      _ = Fintype.card (Pair (Fin n)) := hpair.symm
      _ = (completeEdges (V := Fin n)).card := hcard
  have hmono : ∀ k : ℕ, m + k ≤ (completeEdges (V := Fin n)).card →
      simpleProbability (V := Fin n) q (m + k) ≤ simpleProbability (V := Fin n) q m := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have hstepValid : (m + k) + 1 ≤ (completeEdges (V := Fin n)).card := by omega
        have hstep := simpleProbability_succ_le q n (m + k) hstepValid
        exact hstep.trans (ih (by omega))
  have hmk : m + (m' - m) ≤ (completeEdges (V := Fin n)).card := by omega
  have hresult := hmono (m' - m) hmk
  have hrepr : m' = m + (m' - m) := by omega
  rw [hrepr]
  exact hresult

end ThLean.W.SA71

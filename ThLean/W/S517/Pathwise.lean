import ThLean.BP.S5.Identification

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S517

open ThresholdFoundations ThLean.BP.S5

private theorem processGraph_subgraph {V : Type} [Fintype V]
    (ω : EdgeStream V) {m n : ℕ} (hmn : m ≤ n) :
    subgraph (processGraph ω m) (processGraph ω n) := by
  intro e
  change
    (Finset.univ.filter (fun i : Fin m => (ω i.val).val = e)).card ≤
      (Finset.univ.filter (fun i : Fin n => (ω i.val).val = e)).card
  apply Finset.card_le_card_of_injOn (fun i : Fin m => Fin.castLE hmn i)
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa using hi
  · intro i hi j hj hij
    exact Fin.castLE_injective hmn hij

private theorem tsum_ennreal_Ico (K H : ℕ) :
    (∑' m : ℕ, if K ≤ m ∧ m < H then (1 : ℝ≥0∞) else 0) = (H - K : ℕ) := by
  rw [tsum_eq_sum (s := Finset.Ico K H)]
  · calc
      (∑ m ∈ Finset.Ico K H, if K ≤ m ∧ m < H then (1 : ℝ≥0∞) else 0) =
          (Finset.Ico K H).card := by
        calc
          (∑ m ∈ Finset.Ico K H,
              if K ≤ m ∧ m < H then (1 : ℝ≥0∞) else 0) =
              ∑ m ∈ Finset.Ico K H, (1 : ℝ≥0∞) := by
            apply Finset.sum_congr rfl
            intro m hm
            simp only [Finset.mem_Ico] at hm
            simp [hm]
          _ = (Finset.Ico K H).card := by simp
      _ = (H - K : ℕ) := by simp [Nat.card_Ico]
  · intro m hm
    have hnot : ¬ (K ≤ m ∧ m < H) := by
      intro h
      exact hm (Finset.mem_Ico.mpr h)
    simp [hnot]

theorem S5_17AStatement_of_deps
    (h04 : ThLean.BP.S5.S5_04Statement)
    (h05 : ThLean.BP.S5.S5_05Statement) :
    ThLean.BP.S5.S5_17AStatement := by
  intro V _ q hq Z hZ ω
  let P : ℕ → Prop := fun m => ¬ Colorable q (processGraph ω m)
  let Q : ℕ → Prop := fun m => ¬ Colorable q (identify (processGraph ω m) Z)
  letI : DecidablePred P := fun m => Classical.propDecidable (P m)
  letI : DecidablePred Q := fun m => Classical.propDecidable (Q m)
  have hImp : ∀ m, P m → Q m := by
    intro m hp hIdent
    exact hp ((h04 V q hq (processGraph ω m) Z hZ).2.2 hIdent)
  constructor
  · by_cases hexP : ∃ m, P m
    · have hexQ : ∃ m, Q m := by
        obtain ⟨m, hm⟩ := hexP
        exact ⟨m, hImp m hm⟩
      have hfind : Nat.find hexQ ≤ Nat.find hexP :=
        Nat.find_min' hexQ (hImp _ (Nat.find_spec hexP))
      simpa [hittingTime, identifiedHittingTime, P, Q, firstFailure, hexP, hexQ] using hfind
    · simp [hittingTime, identifiedHittingTime, P, firstFailure, hexP]
  · intro H htime
    have htime' : firstFailure P = (H : WithTop ℕ) := by
      simpa [hittingTime, P] using htime
    have hexP : ∃ m, P m := by
      by_contra hn
      simp [firstFailure, hn] at htime'
    have hfindH : Nat.find hexP = H := by
      have hcoe : (Nat.find hexP : WithTop ℕ) = (H : WithTop ℕ) := by
        simpa [firstFailure, hexP] using htime'
      exact WithTop.coe_injective hcoe
    have hbadH : P H := by
      rw [← hfindH]
      exact Nat.find_spec hexP
    have hexQ : ∃ m, Q m := ⟨H, hImp H hbadH⟩
    let K := Nat.find hexQ
    have hKtime : identifiedHittingTime q Z ω = (K : WithTop ℕ) := by
      simp [identifiedHittingTime, Q, firstFailure, hexQ, K]
    have hKbad : Q K := by
      dsimp [K]
      exact Nat.find_spec hexQ
    have hKleH : K ≤ H := by
      dsimp [K]
      rw [← hfindH]
      exact Nat.find_min' hexQ (hImp _ (Nat.find_spec hexP))
    have hP_iff : ∀ m, P m ↔ H ≤ m := by
      intro m
      constructor
      · intro hm
        have h := Nat.find_min' hexP hm
        simpa [hfindH] using h
      · intro hHm
        have hsub := processGraph_subgraph ω hHm
        intro hcol
        apply hbadH
        obtain ⟨σ, hσ⟩ := hcol
        exact ⟨σ, fun u v huv => hσ u v (lt_of_lt_of_le huv (hsub (s(u, v))))⟩
    have hQ_iff : ∀ m, Q m ↔ K ≤ m := by
      intro m
      constructor
      · intro hm
        have h := Nat.find_min' hexQ hm
        simpa [K] using h
      · intro hKm
        have hsub := processGraph_subgraph ω hKm
        have hmono := (h05 V q hq).1 (processGraph ω K) (processGraph ω m) Z hZ hsub
        exact hmono.2 hKbad
    have hColorable_iff : ∀ m, Colorable q (processGraph ω m) ↔ m < H := by
      intro m
      constructor
      · intro hc
        have hnot : ¬ H ≤ m := by
          intro hHm
          exact ((hP_iff m).2 hHm) hc
        omega
      · intro hlt
        by_contra hc
        have hHm := (hP_iff m).1 hc
        omega
    have hEvent : ∀ m,
        (Colorable q (processGraph ω m) ∧
          ¬ Colorable q (identify (processGraph ω m) Z)) ↔
          K ≤ m ∧ m < H := by
      intro m
      simp only [← hColorable_iff m, ← hQ_iff m]
      tauto
    refine ⟨K, hKtime, hKleH, ?_⟩
    simp only [hEvent]
    exact (tsum_ennreal_Ico K H).symm

example (h04 : ThLean.BP.S5.S5_04Statement)
    (h05 : ThLean.BP.S5.S5_05Statement) :
    ThLean.BP.S5.S5_17AStatement :=
  S5_17AStatement_of_deps h04 h05

end ThLean.W.S517

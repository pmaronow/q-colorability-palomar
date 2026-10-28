import ThLean.BP.S6.Foundation

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S608

private theorem relation_mem_iff (n q : ℕ) (G : ThLean.BP.S6.Graph n) (u a b : Fin n) :
    (a, b) ∈ relation q G u ↔
      Colorable q G ∧ ¬ Frozen q G u a ∧ ¬ Frozen q G u b ∧
        ∀ σ, IsColoring q G σ → (σ u = σ a ∨ σ u = σ b) := by
  simp [relation]

private theorem relation_card_sections (n q : ℕ) (G : ThLean.BP.S6.Graph n) (u : Fin n) :
    (relation q G u).card = ∑ a : Fin n, (relationSection q G u a).card := by
  classical
  let R := relation q G u
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := R) (t := Finset.univ) (f := Prod.fst)
    (fun _ _ => Finset.mem_univ _)
  have hfiber (a : Fin n) :
      (R.filter (fun p : Fin n × Fin n => p.1 = a)).card =
        (relationSection q G u a).card := by
    let F := R.filter (fun p : Fin n × Fin n => p.1 = a)
    have himage : F.image Prod.snd = relationSection q G u a := by
      ext v
      simp [F, R, relationSection]
    have hinj : Set.InjOn Prod.snd (F : Set (Fin n × Fin n)) := by
      intro p hp p' hp' heq
      change p ∈ F at hp
      change p' ∈ F at hp'
      have hp1 := (Finset.mem_filter.mp hp).2
      have hp'1 := (Finset.mem_filter.mp hp').2
      apply Prod.ext
      · exact hp1.trans hp'1.symm
      · exact heq
    calc
      F.card = (F.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
      _ = (relationSection q G u a).card := by rw [himage]
  calc
    R.card = ∑ a ∈ (Finset.univ : Finset (Fin n)),
        (R.filter (fun p : Fin n × Fin n => p.1 = a)).card := hcard
    _ = ∑ a : Fin n, (relationSection q G u a).card := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hfiber a

theorem S6_05Statement_holds : ThLean.BP.S6.S6_05Statement := by
  classical
  intro n q hn hq G u
  constructor
  · intro a b
    change (a, b) ∈ relation q G u ↔ (b, a) ∈ relation q G u
    constructor
    · intro hab
      rcases (relation_mem_iff n q G u a b).mp hab with
        ⟨hc, hna, hnb, hprop⟩
      apply (relation_mem_iff n q G u b a).mpr
      exact ⟨hc, hnb, hna, fun σ hσ => (hprop σ hσ).symm⟩
    · intro hba
      rcases (relation_mem_iff n q G u b a).mp hba with
        ⟨hc, hnb, hna, hprop⟩
      apply (relation_mem_iff n q G u a b).mpr
      exact ⟨hc, hna, hnb, fun σ hσ => (hprop σ hσ).symm⟩
  constructor
  · intro a ha
    have hmem := (relation_mem_iff n q G u a a).mp ha
    rcases hmem with ⟨hc, hna, _, hprop⟩
    have hfrozen : Frozen q G u a :=
      ⟨hc, fun σ hσ => (hprop σ hσ).elim id id⟩
    exact hna hfrozen
  constructor
  · intro a v hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    have hrel : (a, v) ∈ relation q G u := by
      simpa [relationSection] using hv
    have hnot := (relation_mem_iff n q G u a v).mp hrel |>.2.2.1
    simpa [frozenClass] using hnot
  constructor
  · intro a ha
    have hfrozen : Frozen q G u a := by
      simpa [frozenClass] using ha
    ext v
    simp [relationSection, relation, hfrozen]
  constructor
  · exact relation_card_sections n q G u
  constructor
  · unfold beta
    positivity
  constructor
  · unfold beta
    have hcardN : (relation q G u).card ≤ n * n := by
      calc
        (relation q G u).card ≤ Fintype.card (Fin n × Fin n) := Finset.card_le_univ _
        _ = n * n := by simp
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hcardR : ((relation q G u).card : ℝ) ≤ (n : ℝ) * n := by
      exact_mod_cast hcardN
    rw [Fintype.card_fin, div_le_one (sq_pos_of_pos hnR)]
    nlinarith
  constructor
  · intro hc
    constructor
    · have huu : u ∈ frozenClass q G u := by
        simp [frozenClass, Frozen, hc]
      exact Finset.one_le_card.mpr ⟨u, huu⟩
    · calc
        (frozenClass q G u).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
        _ = n := by simp
  · intro hnc
    constructor
    · ext p
      simp [relation, hnc]
    · simp [beta, relation, hnc]

end ThLean.W.S608

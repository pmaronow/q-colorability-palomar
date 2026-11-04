module

public import ThLean.W.S559S.Averages
public import ThLean.W.S559.Poisson

@[expose] public section

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S559S
open ThresholdFoundations ThLean.BP.S5

private lemma kappa_range {V : Type} [Fintype V] (q : ℕ) (G : MGraph V) :
    0 ≤ kappa q G ∧ kappa q G ≤ 1 := by
  unfold kappa uniformProb
  exact uniformMean_range _ (fun _ => indicator_range _)

/-- Exchangeability converts the normalized root partner mean to the hazard. -/
lemma normalized_partner_graphMean (h12 : S5_12Statement)
    (h08 : S5_08BStatement) (hE01 : S5_E01Statement)
    {V : Type} [Fintype V] (q : ℕ) (hq : 3 ≤ q) (hV : 2 ≤ Fintype.card V)
    (t : ℝ) (ht : 0 ≤ t) :
    poissonGraphMean t (fun G : MGraph (Option V) =>
      (1 / (Fintype.card V : ℝ)) * (partnerCount q G none : ℝ)) =
      poissonGraphMean (V := Option V) t (kappa q) := by
  have hK : 2 ≤ Fintype.card (Option V) := by simp only [Fintype.card_option]; omega
  let r : ℝ := t / ((Fintype.card (Option V)).choose 2 : ℝ)
  have hr : 0 ≤ r := div_nonneg ht (Nat.cast_nonneg _)
  have h := (h12 (Option V) q hq hK (countPMF h08 hE01 hK r hr)
    (countPMF_invariant h08 hE01 hK r hr) none).2.2
  rw [lawMean_countPMF, lawMean_countPMF] at h
  have hcard : (Fintype.card (Option V) : ℝ) - 1 = Fintype.card V := by
    simp [Fintype.card_option]
  rw [hcard] at h
  have hnorm : countMean r (fun G : MGraph (Option V) =>
      (1 / (Fintype.card V : ℝ)) * (partnerCount q G none : ℝ)) =
      countMean (V := Option V) r (kappa q) := by
    rw [countMean_mul_left]
    simpa only [one_div_mul_eq_div] using h
  have hf : ∃ C : ℝ, ∀ G : MGraph (Option V),
      |(1 / (Fintype.card V : ℝ)) * (partnerCount q G none : ℝ)| ≤ C := by
    refine ⟨1, fun G => ?_⟩
    rw [abs_of_nonneg (normalized_partner_range hV q G).1]
    exact (normalized_partner_range hV q G).2
  have hk : ∃ C : ℝ, ∀ G : MGraph (Option V), |kappa q G| ≤ C := by
    refine ⟨1, fun G => ?_⟩
    have hG := kappa_range q G
    rw [abs_of_nonneg hG.1]
    exact hG.2
  exact (h08 (Option V) hK t ht _ hf).trans
    (hnorm.trans (h08 (Option V) hK t ht _ hk).symm)

/-- The root-increment mean equals the augmented-graph hazard after Poisson mixing. -/
lemma mean_increment_hazard_of_deps (h13 : S5_13Statement)
    (h15A : S5_15AStatement) (h12 : S5_12Statement)
    (h08 : S5_08BStatement) (hE01 : S5_E01Statement)
    {V : Type} [Fintype V] (q : ℕ) (hq : 3 ≤ q) (hV : 2 ≤ Fintype.card V)
    (rate s : ℝ) (hrate : 0 < rate) (hs : 0 ≤ s) :
    poissonMixture (rate * Fintype.card V * s) (incrementMean (V := V) q (rate * s)) =
      poissonGraphMean (V := Option V)
        (rate * ((Fintype.card V + 1).choose 2 : ℝ) * s) (kappa q) := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  let f : MGraph (Option V) → ℝ := fun G =>
    (1 / (Fintype.card V : ℝ)) * (partnerCount q G none : ℝ)
  have hf : ∀ G, 0 ≤ f G ∧ f G ≤ 1 := normalized_partner_range hV q
  have hbounded : ∃ C : ℝ, ∀ G, |f G| ≤ C := by
    refine ⟨1, fun G => ?_⟩
    rw [abs_of_nonneg (hf G).1]
    exact (hf G).2
  have hinc : ∀ j, incrementMean (V := V) q (rate * s) j =
      countMean (rate * s) (fun B : MGraph V => listMean j (fun xs => f (addRoot B xs))) := by
    intro j
    apply countMean_congr_loopless
    intro B hB
    have h := ((h13 V q hq B hB).2 j).2.2.2.2.2
    simpa only [f, listMean_mul_left] using h
  calc
    poissonMixture (rate * Fintype.card V * s) (incrementMean (V := V) q (rate * s)) =
        poissonMixture (rate * Fintype.card V * s) (fun j =>
          countMean (rate * s) (fun B : MGraph V => listMean j (fun xs => f (addRoot B xs)))) := by
      congr 1
      funext j
      exact hinc j
    _ = countMean (rate * s) (fun B : MGraph V =>
        poissonMixture (rate * Fintype.card V * s)
          (fun j => listMean j (fun xs => f (addRoot B xs)))) := by
      apply poissonMixture_countMean_comm h08 hE01 hV _ _ (by positivity) (by positivity)
      intro B j
      exact uniformMean_range _ (fun _ => hf _)
    _ = poissonGraphMean (rate * ((Fintype.card V + 1).choose 2 : ℝ) * s) f :=
      h15A V hV rate s hrate hs f hbounded
    _ = poissonGraphMean (V := Option V)
        (rate * ((Fintype.card V + 1).choose 2 : ℝ) * s) (kappa q) :=
      normalized_partner_graphMean h12 h08 hE01 q hq hV _ (by positivity)

theorem S5_15BStatement_of_deps (h13 : S5_13Statement)
    (h15A : S5_15AStatement) (h12 : S5_12Statement) (h08B : S5_08BStatement)
    (hE01 : S5_E01Statement) (hE08 : S5_E08Statement) :
    ThLean.BP.S5.S5_15BStatement := by
  intro V _ q hq hV rate s hrate hs
  obtain ⟨hi, hb, hsum⟩ := ThLean.W.S559.S5_15B_first_three_of_deps
    h13 h15A h12 h08B hE01 hE08 V q hq hV rate s hrate hs
  exact ⟨hi, hb, hsum, mean_increment_hazard_of_deps
    h13 h15A h12 h08B hE01 q hq hV rate s hrate hs⟩

section ExactType
variable (h13 : S5_13Statement) (h15A : S5_15AStatement) (h12 : S5_12Statement)
  (h08B : S5_08BStatement) (hE01 : S5_E01Statement) (hE08 : S5_E08Statement)

example : ThLean.BP.S5.S5_15BStatement :=
  S5_15BStatement_of_deps h13 h15A h12 h08B hE01 hE08
end ExactType

end ThLean.W.S559S

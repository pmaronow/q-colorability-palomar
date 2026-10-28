import ThLean.W.S559S.Laws

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S559S
open ThresholdFoundations ThLean.BP.S5

lemma graphMass_eq_zero_of_not_loopless {V : Type} [Fintype V]
    (r : ℝ) (G : MGraph V) (hG : ¬ Loopless G) : graphMass r G = 0 := by
  obtain ⟨v, hv⟩ := not_forall.mp hG
  unfold graphMass independentPoissonGraphMass
  apply Finset.prod_eq_zero (Finset.mem_univ (s(v, v)))
  simp [perPairRate, poissonWeight, hv]

lemma countMean_congr_loopless {V : Type} [Fintype V] (r : ℝ)
    (f g : MGraph V → ℝ) (hfg : ∀ G, Loopless G → f G = g G) :
    countMean r f = countMean r g := by
  unfold countMean independentPoissonGraphMean
  apply tsum_congr
  intro G
  by_cases h : Loopless G
  · rw [hfg G h]
  · change graphMass r G * f G = graphMass r G * g G
    rw [graphMass_eq_zero_of_not_loopless r G h]
    simp

lemma countMean_mul_left {V : Type} [Fintype V] (r c : ℝ) (f : MGraph V → ℝ) :
    countMean r (fun G => c * f G) = c * countMean r f := by
  change (∑' G, graphMass r G * (c * f G)) = c * ∑' G, graphMass r G * f G
  simp_rw [mul_left_comm _ c]
  rw [tsum_mul_left]

lemma listMean_mul_left {V : Type} [Fintype V] (j : ℕ) (c : ℝ) (f : List V → ℝ) :
    listMean j (fun xs => c * f xs) = c * listMean j f := by
  simp only [listMean, uniformMean, ← Finset.mul_sum]
  ring

lemma uniformMean_mul_left {A : Type} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

lemma graphMean_mul_left {V : Type} [Fintype V] (t c : ℝ) (f : MGraph V → ℝ) :
    poissonGraphMean t (fun G => c * f G) = c * poissonGraphMean t f := by
  unfold poissonGraphMean
  simp_rw [uniformMean_mul_left]
  unfold poissonMixture
  simp_rw [mul_left_comm _ c]
  rw [tsum_mul_left]

lemma countMean_range (h08 : S5_08BStatement) (hE01 : S5_E01Statement)
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (r : ℝ) (hr : 0 ≤ r) (f : MGraph V → ℝ)
    (hf : ∀ G, 0 ≤ f G ∧ f G ≤ 1) :
    0 ≤ countMean r f ∧ countMean r f ≤ 1 := by
  have hs := graphMass_hasSum h08 hE01 hV r hr
  have hf0 : ∀ G, 0 ≤ graphMass r G * f G := fun G =>
    mul_nonneg (graphMass_nonneg hr G) (hf G).1
  have hle : ∀ G, graphMass r G * f G ≤ graphMass r G := fun G =>
    mul_le_of_le_one_right (graphMass_nonneg hr G) (hf G).2
  have hsf : Summable (fun G => graphMass r G * f G) :=
    Summable.of_nonneg_of_le hf0 hle hs.summable
  refine ⟨tsum_nonneg hf0, ?_⟩
  change (∑' G, graphMass r G * f G) ≤ 1
  rw [← hs.tsum_eq]
  exact hsf.tsum_le_tsum hle hs.summable

/-- Interchange the independent background and list-length averages. -/
lemma poissonMixture_countMean_comm (h08 : S5_08BStatement) (hE01 : S5_E01Statement)
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z) (f : MGraph V → ℕ → ℝ)
    (hf : ∀ G j, 0 ≤ f G j ∧ f G j ≤ 1) :
    poissonMixture z (fun j => countMean r (fun G => f G j)) =
      countMean r (fun G => poissonMixture z (f G)) := by
  have hsG := (graphMass_hasSum h08 hE01 hV r hr).summable
  have hsj := (hE01.1 z hz).2.1.summable
  have hw : ∀ j, 0 ≤ poissonWeight z j := fun j => ((hE01.1 z hz).1 j).1
  have hsprod := hsj.mul_of_nonneg hsG hw (graphMass_nonneg hr)
  have hs : Summable (fun p : ℕ × MGraph V =>
      poissonWeight z p.1 * graphMass r p.2 * f p.2 p.1) := by
    apply Summable.of_nonneg_of_le (fun p => mul_nonneg
      (mul_nonneg (hw p.1) (graphMass_nonneg hr p.2)) (hf p.2 p.1).1) _ hsprod
    intro p
    exact mul_le_of_le_one_right
      (mul_nonneg (hw p.1) (graphMass_nonneg hr p.2)) (hf p.2 p.1).2
  change (∑' j, poissonWeight z j * ∑' G, graphMass r G * f G j) =
    ∑' G, graphMass r G * ∑' j, poissonWeight z j * f G j
  simp_rw [← tsum_mul_left]
  simp_rw [← mul_assoc]
  rw [← hs.tsum_comm]
  apply tsum_congr
  intro G
  apply tsum_congr
  intro j
  ring

lemma normalized_partner_range {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (q : ℕ) (G : MGraph (Option V)) :
    0 ≤ (1 / (Fintype.card V : ℝ)) * (partnerCount q G none : ℝ) ∧
    (1 / (Fintype.card V : ℝ)) * (partnerCount q G none : ℝ) ≤ 1 := by
  have hcard : 0 < (Fintype.card V : ℝ) := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hc : partnerCount q G none ≤ Fintype.card V := by
    have hsub : (Finset.univ.filter (fun v : Option V => v ≠ none ∧ Frozen q G none v)) ⊆
        Finset.univ.erase none := by
      intro v hv
      simpa using (Finset.mem_filter.mp hv).2.1
    have h := Finset.card_le_card hsub
    simpa [partnerCount, frozenPartnerCount] using h
  constructor
  · positivity
  · rw [one_div_mul_eq_div, div_le_one hcard]
    exact_mod_cast hc

end ThLean.W.S559S
